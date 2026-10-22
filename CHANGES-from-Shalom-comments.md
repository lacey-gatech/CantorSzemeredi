# Revision record: Or Shalom's comments and the adversarial referee report

The paper compiles cleanly (`latexmk -pdf main.tex`), 31 pages: no LaTeX or package warnings — so no
undefined references or citations — and no overfull lines. These were checked with a byte-safe
search of the log, which was itself tested against planted warnings; see §16 for why that matters. Originals of every edited file are in `backup-pre-edit/` (read-only). Snapshots before
each phase of the referee revision are in `backup-phaseA/` … `backup-phaseF/`; the revision plan is
`Report/Revision_Plan_verified.md`.

This summary was rewritten on 17 October, after the referee revision, and replaces the one written
on 16 October. Sections 1–16 below are the chronological record; where an earlier section claimed
something later found to be wrong, it carries a note saying so.

---

## Summary

**What the paper proves, and how.** Theorem 1.2: for every invertible measure preserving system,
the uniform averages `E_{M≤n<N} ∫ ∏_{j≤ℓ} T^{j k_n} f` have a positive liminf as `N−M → ∞`. Hence
the good indices form a syndetic set (Corollary 1.4) and, via correspondence, Theorem 1.5 on
integers. The proof is the maximal-factor argument, with every step written out:

- (W) a weakly mixing extension of a CSZ factor is CSZ — Lemma 3.2;
- (K) a compact extension of a CSZ factor is CSZ — Theorem 5.1;
- chains of CSZ factors have CSZ suprema — Lemma 2.25;
- Furstenberg's dichotomy — Lemma 2.27, cited, with the definitions checked against the source;
- the reduction from arbitrary systems to ergodic ones on compact metric spaces — Proposition 2.30.

The arithmetic of the Cantor set enters through the block identities (Lemma 2.10) and the uniform
exponential-sum bound (Lemma 2.13), both now proved in the paper. The first paper is cited only for
attribution and context. What remains cited is standard: the dichotomy and the localisation lemma
for compact extensions (Furstenberg; Moreira 8.6.1, 8.4.3), disintegration and ergodic decomposition
(Moreira 7.2.1, 7.3.1), Wiener's lemma, the monotone class theorem.

**Round 1 — Or Shalom's letter (16 October).** The framing was corrected: the paper does not extend
Furstenberg–Katznelson, whose IP theorem already applies to Cantor sets; the contribution is the
*frequency* of good differences. The conclusion was upgraded to syndeticity, and the old Theorem 1.2,
which needed an interchange of limits, was replaced by Theorem 1.5 (§§1–3). Reading the paper closely
then turned up the failure of the van der Waerden route for compact extensions — it produces
dilates, and Cantor sets are not closed under dilation — and §5.1 was rebuilt on the
Furstenberg–Katznelson–Ornstein argument (§6). There were also repairs to §4 (§4, §8).

**Round 2 — the adversarial referee (17 October).** Every point was checked against the source.

1. *§3 did not prove what it claimed.* The van der Corput lemma needs `E_h |E_n⟨u_{n+h},u_n⟩|`
   small, and both proofs bounded only `|E_h E_n⟨u_{n+h},u_n⟩|`. This is in text I rewrote on
   16 October and described as fixed (§7(b)). Repaired in Phase A (§11) by bounding each shift with
   a non-negative quantity before averaging.
2. Not raised by the referee: Lemma 3.12 also misquoted its own induction hypothesis — the shifts on
   the conditional expectations were dropped — and compared functions on different spaces. Both
   repaired in Phase A.
3. *A compact system need not have rational spectrum.* The old Theorem 5.1 depended on that, and so
   did the route to compact systems (Phase B, §12). I had read past this sentence three times.
4. *Chain closure and the maximality step were not proved* (Phase C, §13). Checking the dichotomy's
   source showed our definition of a weakly mixing extension asked for more than that source
   delivers; aligned.
5. *The reductions were undocumented,* and a uniform liminf needs Fatou's lemma along a realising
   sequence of windows rather than directly (Phase D, §14).
6. *The Cantor input was imported* from the first paper and is now proved here (Phase E, §15).

**Where a second pair of eyes is most useful.**

1. **Lemma 3.2 (§3), the non-negativity argument.** It is new mathematics, it is my work, and it is
   the step that was wrong before. The heart is Step 1, (3.7): each shift is bounded by a
   non-negative `φ`, using the induction hypothesis *with* its shifts. Cauchy–Schwarz then passes to
   `ψ ≥ φ²`, which is the Fourier transform of a positive, atomless measure on the relatively
   independent self-joining (Lemma 2.6).
2. **Theorem 5.1 (§5.1), compact extensions.** New in round 1. The referee found it sound, but it
   too is my work.
3. **The adapted classical steps:** chains (Lemma 2.25), the reduction (Proposition 2.30), and the
   alignment of definitions with Moreira's notes (after Lemma 2.27).
4. **The characterisation of Kra–Shalom in the introduction** is still written from Shalom's own
   description, not from their paper.

**Numbering: the referee's version against the revised one.** For the response letter. Results
marked — were removed (left column) or are new (right column).

| Kind | Referee's version | Revised | Label |
|---|---|---|---|
| Theorem | 1.2 | 1.2 | `t:CSZ` |
| Corollary | 1.4 | 1.4 | `c:syndetic` |
| Theorem | 1.5 | 1.5 | `t:CSZ-Integers` |
| Remark | 1.7 | 1.7 | `r:order` |
| Remark | 1.8 | 1.8 | `r:novelty` |
| Section | — | 2 | `s:prelim` |
| § | 2.2 | 2.2 | `sub:mps` |
| Proposition | 2.3 | — | `productweakly` |
| § | — | 2.5 | `sub:reduction` |
| Lemma | 2.6 | — | `l:mixed` |
| Lemma | — | 2.6 | `l:atomless` |
| Lemma | 2.10 | 2.10 | `l:Diff` |
| Lemma | 2.11 | 2.11 | `l:differences` |
| Lemma | 2.12 | — | `l:Allq` |
| Lemma | 2.13 | 2.12 | `l:syndeticResidues` |
| Lemma | 2.14 | 2.13 | `l:irrational` |
| Theorem | 2.16 | — | `CantorErgodic` |
| Lemma | — | 2.17 | `l:uniformSpectral` |
| Theorem | 2.18 | — | `t:Progressions` |
| Theorem | 2.22 | 2.20 | `t:ECSZ` |
| Lemma | 2.23 | 2.21 | `l:powers` |
| Lemma | — | 2.25 | `l:chain` |
| Lemma | 2.26 | 2.24 | `l:Extensions` |
| Lemma | — | 2.27 | `l:dichotomy` |
| Lemma | 2.28 | 2.28 | `vdC` |
| Proposition | — | 2.30 | `p:reduction` |
| Section | 3 | 3 | `sec:wm` |
| Theorem | 3.1 | 3.4 | `t:wm` |
| Lemma | 3.12 | 3.2 | `l:wmExtension` |
| Section | 4 | 4 | `sec:vdW` |
| Theorem | 4.1 | 4.1 | `thmCvdW` |
| Corollary | 4.2 | 4.2 | `c:vdW` |
| Theorem | 4.3 | 4.3 | `thm:2` |
| Lemma | 4.4 | 4.4 | `lem:1` |
| Section | 5 | 5 | `sec:compact` |
| Theorem | 5.1 | 5.17 | `t:compactSystem` |
| § | — | 5.2 | `sub:rootsOfUnity` |
| Theorem | 5.3 | 5.1 | `t:compactExtension` |
| Lemma | 5.7 | 5.5 | `l:localize` |
| Lemma | 5.10 | 5.8 | `l:unfortunate` |
| Lemma | 5.13 | 5.11 | `l:returnTime` |
| Remark | 5.18 | 5.16 | `r:dilation` |

---

## Chronological record

## 1. Framing (Shalom §1.1, §1.2, §2.1(1))

The claims that the paper "extends" the Furstenberg–Katznelson IP theorem and "partially extends"
Kra–Shalom are removed from the abstract and the introduction. In their place:

- Theorem A is now the FK IP Szemerédi theorem (`FK85`, Theorem A), stated for powers of a single
  transformation, together with the observation that **via correspondence it is already a density
  statement** — indeed that the set of good differences `G(A,ℓ)` is an IP\* set, hence syndetic.
- It is stated explicitly that a Cantor set with `0 ∈ D` contains an IP-set, so that FK and
  Kra–Shalom **apply directly to Cantor sets**, and that the implication runs IP ⟹ Cantor, not the
  other way. The sentence "It seems very plausible that many of the results of Kra and Shalom can be
  extended to the Cantor sets" is gone.
- New Remark 1.8 isolates the contribution as a **frequency** statement, along the lines of §1.3 of
  the letter.
- Acknowledgment to Or Shalom added.
- New bibliography entry `FK85` (J. Analyse Math. 45 (1985), 117–168). No MR number was added, as
  it was not verified.

## 2. Syndeticity (Shalom §1.3, §2.1(2))

All averages over the index are now **uniform**, i.e. `lim_{N-M→∞} E_{M≤n<N}`. This is the form that
yields syndeticity, and it is carried through the whole paper:

- Definition of the CSZ property (2.4) now uses uniform averages, eq. `(e:CSZdef)`.
- Corollary 1.4: uniform averages with positive liminf ⟹ the set of good indices is syndetic.
- Theorem 1.5 (the integer statement) now concludes that `B = {n : k_n ∈ G(A,ℓ)}` is **syndetic**.
- **New Lemma 2.13**: for every `q`, `{n : q | k_n}` is syndetic (not merely of positive density,
  which is all Lemma 2.12 gives, and uniform convergence genuinely fails there). The proof uses the
  block structure `k_{δ^i n + j} = b^i k_n + k_j` and the fact that a finite sub-semigroup of `Z_q`
  is a subgroup. This is what upgrades the compact-system case to syndeticity.
  *Superseded (17 Oct): that upgrade went through the old Theorem 5.1, which relied on a false
  spectral claim; compact systems are now handled by Theorem 5.1 over the trivial factor (§12).*
- **Theorem 2.18** now also proves the uniform ergodic theorem `(e:Uniform)` from `[firstpaper,
  (4.8)]` by a spectral-measure argument, and adds a uniform ergodic theorem **along progressions**
  of step a power of `δ`, which is what the induction in §3 needs in the uniform setting.
- §3 (weak mixing, weak mixing extensions) rewritten with uniform averages throughout; the choice of
  `Δ^#(h)` is now made from *finitely many* progressions, so that its density is attained uniformly
  over long intervals.

## 3. Theorem 1.2 vs Theorem 1.3 (Shalom §2.2(3))

The old Theorem 1.2 averaged over `x ∈ [N]` and `n ∈ [N]` simultaneously, and did not follow from
the ergodic theorem. It is replaced by Theorem 1.5, proved by applying the correspondence principle
**for one index `n` at a time** — no interchange of limits is involved, and the conclusion is
stronger. New Remark 1.7 records explicitly why the simultaneous average is not a formal consequence.

## 4. Repair in §4 (van der Waerden)

The color-focusing Lemma had a gap: with `r = r_0 + b^h r_1`, the new generator `k_J = b^h r_1` is
zero whenever `r < b^h`, which breaks condition (1). Theorems 4.1 and 4.3 now carry an auxiliary parameter
`h` and produces a difference in `b^h C \ {0}`; the induction then supplies a generator at scale
`≥ b^{h'}` directly, so `k_J = r` and the `r_0` correction disappears. Also:

- condition (1) corrected to `0 ≤ j < j' ≤ J` (for `j = j'` the sum is empty, hence `0 ∉ C\{0}`);
- condition (2) now includes `x_j ∈ U_{α_j}`;
- Zorn's lemma argument corrected (minimal **non-empty** closed invariant set; chains have non-empty
  intersection by compactness);
- the reduction from the cover to a single open set `U` is now justified;
- the progression length is called `ℓ` throughout (it was variously `n`, `k`, `ℓ`);
- new Corollary 4.2 states the finitary coloring form that §5 actually uses.

## 5. Smaller corrections

- Enumeration is `0 = k_0 < k_1 < ⋯` everywhere (was `0 = k_1 < k_2 < ⋯`, inconsistent with
  Lemma 2.10 and with the first paper).
- Digit set is `D ⊂ {0,…,b−1}`; the paper had `D ⊂ [b] = {1,…,b}`, which excludes `0 ∈ D`.
- Notation unified to `C` for the Cantor set (was `K` and `C` interchangeably); `δ = |D|`.
- Lemma 2.10: `n ∈ N_0`; the garbled "we do not allow leading zeroes … unless `0 ∉ D`" note removed.
- Products `∏_{s=0}^t T^{s k_n} f` corrected in several places where the `s` had been dropped
  (Theorem 5.1, Theorem 5.3, and in §3).
- The inner-product expansion in §3 was garbled (`T^{s k_{n+h} − k_n}`); rewritten.
- Lemma 2.26(4): the hypothesis that `D` is CSZ was missing.
- Theorem 5.3 no longer assumes the factor is ergodic; the proof does not use it.
- Conditional weak mixing definition was missing its limit.
- `μ` / `m` typos, `\langle T^{s_0 n} f_{s_0}, g_s\rangle` → `g_{s_0}`, "poof" → "proof",
  "we can a finite collection" → "we can find", `E(F|D^t)^2` → `‖E(F|D^t)‖^2`,
  Cauchy–Schwartz → Cauchy–Schwarz, `e^{2πα k_n}` → `e(α k_n)`.
- `[firstpaper]*{(4.6)}` → `(4.8)`; (4.6) is the definition of the exceptional set, the uniform
  limit is (4.8), in Lemma 4.5 of that paper.
- The two "further questions" bullets referred to `ℓ = 2`; in the present normalization the
  Sárközy-type results of the first paper are the case `ℓ = 1`.

## 6. The compact-extension step: rebuilt (was the one unresolved point)

The van der Waerden argument for Theorem 5.3 does **not** prove the stated theorem, and this is a
pre-existing problem, independent of Shalom's comments. Running van der Waerden in the variable `w`
for a fixed averaging parameter `n` produces a monochromatic progression `w_0, w_0+k, …, w_0+tk`,
so the common difference of the resulting configuration is `k·n` — a **dilate** of `n`. In the
classical setting this is harmless: `Z` is closed under dilation, so one pigeonholes over the finitely
many `k` and notes that the multiples of a fixed `k` have positive density (this is the last line of
Furstenberg's argument). **A Cantor set is not closed under dilation**, so the step does not transfer:
neither `k·n` nor `k·k_n` lies in `C` in general. The same objection applies to the original
positive-density statement, not just to the syndetic one.

The fix is to use the *other* classical proof — the one of Furstenberg, Katznelson and Ornstein,
which avoids van der Waerden and works natively with uniform Cesàro limits (presented in Moreira's
notes, §8.5). What that argument produces is a return time `n + a`, where `a` ranges over a **fixed
finite set** `F` — a *translate*, not a dilate. Translates are exactly what the Cantor set can
absorb: if `F ⊂ C ∩ [0, b^i)` and `n ∈ b^i C`, then by Lemma 2.10(ii)

        n + a = b^i k_u + a = k_{δ^i u + ι(a)} ∈ C,

and the index moves only inside the block `[δ^i u, δ^i (u+1))`. §5 has been rewritten along these
lines:

- "unfortunate sets" `F` are taken to be subsets of `C` rather than of `Z`; Lemma 5.10 (large sets are
  not unfortunate) is unaffected, as it is pure pigeonholing;
- the scale `i` is fixed after `F`, by `F ⊂ C ∩ [0, b^i)` (5.12);
- the averaging parameter is `n = b^i k_u`, so that `F + n ⊂ C` and the maximality argument
  (Lemma 5.13) runs inside `C`;
- the good indices `v(u) = δ^i u + ι(a_u)` hit the block of every `u ∈ B`, and `B` has positive
  lower *uniform* density by the CSZ hypothesis on `D`, so the conclusion follows with a loss of
  `δ^{-i}`.

**One structural change this forces.** The argument uses the hypothesis on the factor `D` at the
dilated scale `b^i`, and returns the conclusion for `E` at scale `1`. So the CSZ property (2.4) now
carries a dilation parameter `i ≥ 0`, i.e. it asserts the bound for each of the systems `(X, T^{b^i})`
— equivalently, for the index restricted to each progression `δ^i N_0`, since `b^i k_n = k_{δ^i n}`.
This is cost-free in the other three cases: new Lemma 2.23 records that weak mixing, compactness, and
weak-mixing and compact extensions all pass to `T^{b^i}`. (For weak-mixing extensions this uses that
a Cesàro limit of a bounded non-negative sequence vanishes iff the sequence tends to 0 on a set of
density one, and that such a set meets every progression in relative density one.)

**Van der Waerden is now unused.** §4 is retained as a result of independent interest, with a
sentence saying so; Corollary 4.2 (the finitary coloring form) is no longer called on. The repair of
the color-focusing lemma described in §4 above still stands on its own.

**Details checked on a second pass.**

- Lemma 2.23(3) is now stated as a transfer principle: if `E_N ‖ |⟨T^n f,g⟩_{E|D}| ‖_{L²(D)} → 0` for
  `f,g` in the Hilbert module, the same holds along `kN`. Stating it for a general `g` matters,
  because §3 uses the mixed form (in verifying that `E^t` is a weakly mixing extension of `D^t`),
  whereas the *definition* of a weakly mixing extension only supplies `g = f`. The proof passes from
  `‖E_N φ_n‖_{L²}→0` to `E_N ‖φ_n‖_{L²}→0` using that the `φ_n` are non-negative and uniformly
  bounded (conditional Cauchy–Schwarz, `f,g` in the module), then uses the density-one
  characterisation. The uniform bound is what makes the two forms equivalent, so the module
  hypothesis is not cosmetic.
- Theorem 5.3 no longer assumes the factor is ergodic. The argument does not use it, and the
  reduction to `T^{b^i}` would not have preserved it — `T^{b^i}` need not be ergodic.
- In the choice of the map `q: F² → [t]`, the index `s` that witnesses a failed pair is necessarily
  `≥ 1`, since `s = 0` reads `0 ≥ ε`; this is now stated, as it is what keeps `s` in the range where
  `T^{sn}x ∈ E` is available.
- `ε` is now fixed up front by (5.8), `(δ_0/2)^{t+1} − tε > 0`, so that it depends only on `t` and
  `δ_0` and everything else depends on it — there is no circularity. The unrelated `ε` used to
  localise `f` was renamed `η`.
- `ι(a_u) < δ^i` is justified: since `0 ∈ D`, the first `δ^i` elements of `C` are exactly
  `C ∩ [0,b^i)` (Lemma 2.10(i)).
- The final count is stated as a liminf rather than as a bound "for `Q−P` large", which was slightly
  too strong as written: `|B ∩ [⌈P/δ^i⌉, ⌊Q/δ^i⌋)|` is bounded below using the lower *uniform*
  density of `B` over an interval of length `≥ (Q−P)/δ^i − 2`, and that interval's length over
  `Q−P` tends to `δ^{-i}`.
- The telescoping behind the conditional Cauchy–Schwarz step is spelled out: `∏_{s=0}^t T^{sd}f −
  f^{t+1}` is a sum of `t` terms (the `s=0` term vanishes), each bounded via one application of the
  conditional Cauchy–Schwarz inequality, giving the loss `tε`.

## 7. Line-by-line pass over Sections 2 and 3

Three genuine gaps, all pre-existing, plus some tightening.

**(a) The induction in Theorem 3.1 did not close.** The proof expands each `f_s` into its mean plus a
mean-zero part and says the induction hypothesis handles every term with at least one constant
factor. But after pulling the constants out, the surviving product runs over a *subset* of the
exponents `{1,…,t}` — say `T^{2k_n}f_2 · T^{5k_n}f_5` — whereas the inductive statement was only
about the consecutive exponents `1,…,t-1`. The van der Corput step has the same problem: it replaces
the exponents by the differences `s_j − s_1`.

Both are fixed by stating Theorem 3.1 and Lemma 3.12 for an arbitrary increasing tuple of positive
exponents `0 < s_1 < ⋯ < s_t`, which is the standard form of Furstenberg's weak-mixing theorem. The
proofs are otherwise unchanged; subtracting the *smallest* exponent keeps everything positive.
Proposition 2.3 is generalised to match. A bonus: the dilation parameter `i` of (2.21) is now just
the case `s_j = j b^i`, so §3 no longer needs to pass to `T^{b^i}` separately.

> **Superseded (17 Oct).** This item claimed a repair that was not one. Bounding the `h`-average of the
> correlations bounds `|E_h E_n⟨u_{n+h},u_n⟩|`; the van der Corput lemma needs `E_h |E_n⟨u_{n+h},u_n⟩|`.
> The referee caught it. The actual repair is §11.

**(b) The last step of Theorem 3.1 was stated incorrectly.** The old text ended "the left side of
the inner product is at most ε in L² norm", but neither side of `⟨S^{k_{n+h}}F, S^{k_n}F⟩` is small
on its own — both are isometric images of `F`. What is small is the average over `h` *for each fixed
n*: interchanging the two finite averages,

        E_h E_n ⟨S^{k_{n+h}}F, S^{k_n}F⟩ = E_n ⟨ E_{1≤h≤H} S^{k_{n+h}}F , S^{k_n}F ⟩,

and for fixed `n` the inner average runs over the index interval `[n+1, n+H]`, of length `H`, so
(3.3) bounds it by `ε` *uniformly in n*. This is exactly where the uniform ergodic theorem is needed,
rather than the ordinary one — worth saying, since it is the whole reason the uniform averages are
available. The same correction is made at the end of Lemma 3.12, where the old chain went through
`‖E(F | D^t)‖²`; the honest route is that `E(F | D^t) = ⊗ E(f_j | D) = 0`, so the base case applies
to `F` directly.

**(c) The choice of `Δ^♯(h)` was asserted, not proved.** The old proof invoked Lemma 2.10(iii) — each
`N_Δ` is a union of progressions — and then asserted that finitely many could be chosen to cover all
but `ε`. That needs the densities of the `N_Δ` to sum to 1, i.e. that no mass escapes as `Δ → ∞`,
which was not shown. New Lemma 2.11 proves the needed statement directly from the block structure: if
`δ^ℓ > h` and `n ≡ c (mod δ^ℓ)` with `c + h < δ^ℓ`, then adding `h` does not carry past the `ℓ`-th
digit, so

        k_{n+h} − k_n = k_{c+h} − k_c,

a constant on each such residue class. So on a union of `δ^ℓ − h` residue classes — density
`1 − hδ^{-ℓ}`, attained uniformly — the difference takes at most `δ^ℓ` values, and each level set is
a finite union of progressions of step `δ^ℓ`. Choosing `δ^ℓ > H/ε` serves all `h ≤ H` at once. This
also makes the appeal to the induction hypothesis along progressions concrete, via the reindexing
(3.6).

**Smaller items.**

- Lemma 2.28 (van der Corput) was stated for complex numbers of modulus ≤ 1, but is applied to
  `L²`-valued sequences in §3 and in the Hilbert module in Lemma 3.12. It is now stated for Hilbert
  space vectors, with a remark that the module version holds pointwise with the same proof.
- Lemma 3.12's conclusion had the second product outside the average; both products are now inside.
- Added after (2.21): the CSZ property for indicators is equivalent to the same property for
  non-negative `f ∈ L^∞` not identically zero (take `A = {f > c}` and use `f ≥ c·1_A`). This is what
  lets Lemma 3.12 conclude the CSZ property for `E` from that of `D`, a deduction that was previously
  left implicit, and it also identifies the `i = 0` case of (2.21) with Theorem 1.2.
- Lemma 2.10(iii) is now unused — Lemma 2.11 replaces it in §3. It is quoted from the companion paper,
  so we left it in; drop it if you prefer.

## 8. Line-by-line pass over Section 4

Two real problems, both in the plumbing rather than in the Cantor-set content.

**(a) The color-focusing lemma used `T^{-1}`, which is not available.** A topological dynamical
system here is a compact metric space with a *continuous* `T`, not a homeomorphism, and the step
`x_J := T^{-r} y` has no meaning in general. The repair is small: on a *minimal* system `T` is
automatically onto, since `T(X)` is a non-empty closed set with `T(T(X)) ⊂ T(X)`, hence equals `X`.
So a preimage exists, and the proof only ever uses `T^r x_J = y` — any preimage will do. This is now
recorded with the definition of minimality, together with the other consequence used, that every
forward orbit enters every non-empty open set. No invertibility is assumed anywhere in §4.

This matters beyond tidiness: Corollary 4.2 is proved by applying Theorem 4.1 to a shift system, and
the shift we need there is the *one-sided* one, which is not invertible — see (b).

**(b) Corollary 4.2 produced a progression that need not lie in `N`.** The proof passed to "a
bi-infinite extension of `χ`" and the closure of its orbit in `{1,…,L}^Z`. The starting point `w_0`
that comes out of that argument is an arbitrary integer, so the progression `w_0, w_0+r, …` can sit
partly or entirely in the non-positive integers, where `χ` was never given — while the Corollary
asserts `w_0 ∈ [W]`. The fix is to work in `{1,…,L}^N` with the one-sided shift and the closure of
the *forward* orbit `{T^m χ : m ≥ 0}`. Then the point produced is a limit of `T^m χ` with `m ≥ 0`,
the conditions involve only the coordinates in `[1, 1+(ℓ−1)r]`, and `w_0 = m+1 ≥ 1`.

**Smaller items.**

- The order of choice in the inductive step was back to front: `V` was introduced as "to be specified
  below", then used to produce `r`, and only afterwards shrunk. It happens that the constraint on `V`
  involves only data from stage `J−1` and not `r`, so there was no circularity — but the proof now
  fixes `V` first, via the explicit display (4.5), and then applies the induction hypothesis to it.
- The corner case `j = J−1` is now handled explicitly in both (1) and (2), where the sum
  `k_{j+1}+⋯+k_{J-1}` is empty. In (2) the requirement degenerates to `V ⊂ U_{α_{J-1}}`, which is the
  first clause of (2) at the previous stage; in (1) the sum is `0 + k_J`.
- The digit argument in (1) is spelled out: the partial sum lies in `b^h C` and is `< b^{h'}`, so its
  digits occupy positions `h,…,h'−1`, while `k_J ∈ b^{h'} C` occupies positions `≥ h'`; the addition
  involves no carrying, so the total is in `b^h C`.
- Zorn's lemma is now applied to reverse inclusion, as it is a minimal element that is wanted.
- The compactness step at the end of Corollary 4.2 is given as König's lemma rather than as "a
  diagonal argument".

## 9. Line-by-line pass over the abstract and introduction

No errors, but three places where the introduction no longer matched what §§2–5 do, and one claim
worth making because it is what justifies the paper.

**The missing argument for why the theorem is not already known.** The introduction established that
`G` is IP\*, hence syndetic, and then asserted that the frequency question is what is new. It never
said why the two facts about `G` do not already answer it. They do not, and a reader is entitled to
ask:

- Syndeticity of `G` says nothing about `G ∩ C`, because `C` has density zero. A syndetic set can be
  disjoint from a Cantor set outright: if `s = gcd(D) > 1` then `C ⊂ sZ`, and the integers not
  divisible by `s` are syndetic and miss `C` entirely.
- The IP\* property places an element of `G` in every *infinite* IP-set. What is needed here is an
  element of `G` in each block `b^i k_u + (C ∩ [0,b^i))` for some fixed `i` — and those blocks are
  finite, and translated.

This is now a paragraph of its own, and it is also exactly the obstruction that §5.1 has to get
around.

**Other changes.**

- "Theorem A says exactly that `G` is IP\*" is now "it follows that" — the passage runs through the
  correspondence principle, and only in one direction.
- The assertion that an IP\* set is syndetic is now justified in a clause (the complement of a
  non-syndetic set is thick, and a thick set contains an IP-set), since the statement is load-bearing
  for the paragraph above.
- The proof outline said the argument follows Furstenberg's proof of Szemerédi's theorem. Since §5.1
  now follows Furstenberg–Katznelson–Ornstein instead, and for a reason specific to Cantor sets, the
  outline says so and points at §5.
- Theorem 1.2 is stated for all invertible systems, while Theorem 2.22 proves the CSZ property for
  ergodic separable ones. The deduction now points at the standing reductions of §2.2 and at the
  passage from sets to non-negative functions recorded after (2.21), rather than leaving both
  implicit.
- The abstract now says `D` has at least two digits, which the body assumes throughout.

## 10. Review of the argument in §5.1

Re-read against the write-up rather than against the intent. One error, which was mine, and it was
in the bookkeeping rather than in the argument.

**The reduction to `i = 0` was invalid.** The proof opened by fixing `i`, passing to `T^{b^i}`, and
asserting that `D` is CSZ for `T^{b^i}` because "the condition for `(X,D,m,T^{b^i})` with dilation
`j` is the condition for `(X,D,m,T)` with dilation `i+j`". That is true for the Cantor set `C` whose
base is `b`, and false in general: the CSZ property quantifies over *all* Cantor sets, and for a
second Cantor set `C'` of base `b'` the condition for `(X,D,m,T^{b^i})` with dilation `j` involves
the exponent `b^i (b')^j`, which is not `(b')^{i+j}`. So the hypothesis does not transfer to
`T^{b^i}` as a whole.

The argument itself is unaffected, because it never needed that much. It uses the hypothesis on `D`
exactly once, at (5.15), and there only for the *same* Cantor set `C`, at a single dilation. The
proof now says so explicitly at the outset, and the general dilation is handled in new Remark 5.18:
run the proof with `T` replaced by `T^{b^{i_0}}`, where the one appeal to the hypothesis becomes
(5.15) at dilation `i_0 + i`, with `i` the scale (5.12). The remark also records why one cannot
argue via "`(X,D,m,T^{b^i})` is CSZ". The same over-claim was in the commentary after (2.21) in §2
and has been corrected there too.

**The rest checks out.** Verified line by line, with the steps worth naming:

- The pigeonhole in Lemma 5.10 (`M = r^{t+1}+1` tuples in `[r]^{t+1}`), and the fact that `s = 0` is
  not available as a witness of a failed pair, which is what keeps `q` valued in `[t]` and hence
  keeps `T^{s_0 n}x ∈ E` available in Lemma 5.13.
- Equivariance of the conditional norm, `‖T^v h‖_{E|D}(x) = ‖h‖_{E|D}(T^v x)`, which is what moves
  (5.11) from the point `T^{s_0 n}x` to `x` and turns a failed pair in `F` into a failed pair in
  `F + n`. This is the hinge of the whole argument.
- `|G| = |F| + 1`: needs `0 ∉ F + n`, which holds because `n = b^i k_u ≥ b^i > max F` for `u ≥ 1`.
- The telescoping behind the conditional Cauchy–Schwarz bound has `t` terms, not `t+1`, since the
  `s = 0` term vanishes; the loss is `tε`, consistent with the choice (5.8) of `ε`.
- `m(J_u) ≥ m(I_u)/|F|` and the passage from `∫_{J_u} E[· | D]` to `∫_X`, which uses `f ≥ 0` and
  `J_u ∈ D`.
- `ι(a_u) < δ^i` because `0 ∈ D` makes the first `δ^i` elements of `C` exactly `C ∩ [0,b^i)`.
- The counting (5.17): `V` meets the block of each `u ∈ B` in exactly one point, blocks inside
  `[P,Q)` correspond to `u ∈ [⌈P/δ^i⌉, ⌊Q/δ^i⌋)`, and that interval's length over `Q−P` tends to
  `δ^{-i}`.
- No circularity in the order of choice: `ε = ε(t,δ_0)`, then `r` and the net, then `M`, then `F`,
  then the scale `i`, then `E`, then `c_0`.
- Ergodicity is not used anywhere, which is why Theorem 5.3 no longer assumes it — and is also what
  makes Remark 5.18 legitimate, since `T^{b^{i_0}}` need not be ergodic.

**Two smaller things fixed.** `A` was being used for two different sets — the localisation set from
Lemma 5.7 and `{g > δ_0/2}`; the former is now `A_*`, and the reason the localisation is harmless
(`0 ≤ f·1_{A_*} ≤ f`, all factors non-negative) is stated rather than left as "it clearly suffices".
Lemma 5.7 was quoted without proof or source; it now cites Moreira, Lemma 8.4.3.

## 11. Phase A of the referee revision: the weak-mixing branch

Responds to the adversarial referee report of 17 October, points 1 and 2, following
`Report/Revision_Plan_verified.md` §2. Snapshot before this phase: `backup-phaseA/`.

**What was wrong.** Three errors, all in §3:

1. Both proofs needed `E_h |E_n⟨u_{n+h},u_n⟩|` small, as the van der Corput lemma requires, and
   bounded only `|E_h E_n⟨u_{n+h},u_n⟩|`. The per-shift correlations are genuinely not small — for
   `h = 1`, `k_{n+1} − k_n` is the smallest nonzero digit for a positive proportion of `n` — so the
   gap was real. My 16 October pass described this endgame as fixed; it was not (see the notes on §7(b)
   and Summary item 3).
2. Lemma 3.12's induction display dropped the shifts `T^{(s_j−s_1)k_n}` from the conditional
   expectations, so it did not follow from the induction hypothesis it cited.
3. Lemma 3.12 identified a function on `X` with one on `X^t` under product measure.

**The repair.** Bound each shift separately, by a non-negative quantity, and only then average over
`h`. For fixed `h`, on each residue class of Lemma 2.12, the induction hypothesis — now quoted with
its shifts, (3.10) — and the `D`-measurability of the result reduce the correlation to the single
function `f = f_{j_0}` with zero conditional expectation:

        |E_n ⟨u_{n+h}, u_n⟩| ≤ E_n φ(s(k_{n+h} − k_n)) + 3ε,      φ(m) = ‖⟨T^m f, f⟩_{E|D}‖_{L¹(D)}.   (3.7)

The triangle inequality runs the right way here. After averaging over `h`, Cauchy–Schwarz passes
to `ψ(m) = ‖⟨T^m f, f⟩_{E|D}‖²_{L²(D)}`, which is `⟨R^m G, G⟩` on the relatively independent
self-joining `λ` with `R = T×T` and `G = f ⊗ f̄`. Because both coordinates carry the same `T`, `λ`
is `R`-invariant, so `ψ` is the Fourier transform of a positive measure `σ`. That measure has no
atoms — directly from the definition of conditional weak mixing, by Wiener's lemma — and the
uniform exponential-sum bound then makes the `h`-average of `ψ` small, uniformly in `n`.

**What changed in the source.**

- §2: new Lemma 2.7 (spectral measures of `f` and of `f ⊗ f̄` are atomless), with the joining `λ`
  and identity (2.6). Lemma 2.15 now states the exact uniform input — the supremum over the starting
  index, and the countable exceptional set `E_0` of `β` with `gcd(D)β` a `b`-adic rational. New Lemma
  2.18 (uniform spectral lemma) replaces old Theorem 2.18. The van der Corput lemma (2.27) is
  restated with correct constants — `4 E_h|c_h| + 2/H`, for `H < N−M` — and now has a proof; the old
  statement had constant `1`, which the standard argument does not give, and an unproved
  Hilbert-module clause, now removed.
- §3 rewritten. Lemma 3.2 (weakly mixing extensions) is proved directly under hypothesis (3.1),
  which is all of relative weak mixing that is used. Old Theorem 3.1 is now Corollary 3.4, the case
  of the trivial factor, with no separate proof.
- Removed: Proposition 2.3 (product systems), Lemma 2.6 (mixed estimate), old Theorem 2.18(ii), the
  product system `X^t`, and the claim that `E^t | D^t` is weakly mixing — so the referee's density
  point (2′) no longer arises. Lemma 2.22(3) now states only what is used: the hypothesis (3.1) passes
  to powers.

**Checks.** The paper builds with no undefined references. Every `h`-average in §3 was audited:
the van der Corput quantity `E_h |E_{M≤n<N−h}⟨·⟩|` is bounded exactly as stated, by averaging the
per-shift bounds (3.7); the only other `h`-average is of the non-negative `ψ`, where nothing crosses an
absolute value. The order of choices is `ε → σ → H → ℓ → L_0 → N−M`, with no circularity.

**Not yet done, by design of the plan.** Lemma 2.22(1) is now used only by Theorem 5.1, which
Phase B removes or restates. The prior-paper input is still cited rather than imported (Phase E).
The standard-Borel assumption behind `λ` is invoked from §2.2's reductions, which Phase D writes out.

**Incident.** While snapshotting for this phase I copied the current `Prelim.tex` and
`weakMixing.tex` over the originals in `backup-pre-edit/`. They were restored from
`~/Downloads/IntegerCantorSets/Cantor Szemeredi/`, which matches the originals in size and in every
distinctive string checked, typos included. That folder is now read-only.

## 12. Phase B of the referee revision: the compact branch

Responds to referee point 3, following `Report/Revision_Plan_verified.md` Phase B, with option (b)
for Theorem 5.1. Snapshot before this phase: `backup-phaseB/`.

**What was wrong.** §2.2 asserted that a compact system "only has rational spectra", and Theorem 5.1
relied on it, choosing `h` with `T^q h = h` close to `f`. Compactness gives pure point spectrum, not
roots of unity: an irrational rotation is compact and fixes no non-constant function under any
`T^q`. So Theorem 5.1 was unproved for compact systems in general, and with it the route to
Lemma 2.25(3). I read past this sentence in three earlier passes.

**What changed.**

- **B1.** §2.2 now says pure point spectrum, and gives the irrational rotation as a compact system
  whose eigenvalues are not roots of unity.
- **B2.** Compact systems are off the main route. A note after Lemma 2.25 records that the trivial
  factor is CSZ (a positive-measure set in it is conull, so every integral in (2.20) is 1), that
  (1) and (3) are the trivial-factor cases of (2) and (4) and are proved that way — Corollary 3.4
  and Theorem 5.3 — and that only (2) and (4) enter Theorem 2.21. Theorem 5.1 is stated to be unused.
- **B3.** Theorem 5.1 is restated for systems in which the functions fixed by some `T^q` are dense —
  equivalently, pure point spectrum with every eigenvalue a root of unity, both directions checked
  and recorded in the text; odometers are examples. Its conclusion is the stronger one the old
  theorem claimed: `∫ ∏_s T^{s k_n} f ≥ ∫ f^{t+1} − ε` on a syndetic set. The proof is new and shorter:
  clip `Re h` to `[0,1]` (still `T^q`-fixed, and no farther from `f`), then a pointwise telescoping
  bound for `[0,1]`-valued products replaces the old Hölder estimate, so an `L¹` approximation is
  enough. The old "in particular, a compact system is CSZ" and its dilation sentence are gone.
  §5's introduction now leads with Theorem 5.3 as the main-route result. Lemma 2.14 (syndetic
  residues) is kept as the support for Theorem 5.1, with its lead-in saying so.
- **B4.** Theorem 5.3: `q` is defined on the ordered off-diagonal pairs `F^(2)`, and the choice of
  `q` is made explicit — the finitely many sets `E_q` are each in `D` and cover `Q(F) ∩ A`, so one
  has positive measure. The selector `a(u,·)` is now the least admissible element in a fixed
  ordering of `F`, with its `D`-measurability spelled out. Of the action plan's other Theorem 5.3
  items, the `u ≥ 1` step, the conditional Jensen line and the `δ^{-i}` loss were already in the text.

**Checks.** Builds clean, no undefined references. Theorem 5.3 and Remark 5.18 keep their numbers,
so references to the referee report still line up.

**Left for Phase F.** Lemma 2.22(1) — powers of weakly mixing and of compact systems — is now
referenced nowhere, since §3 handles dilations through general exponents and Theorem 5.1 no longer
passes to powers. Remove it with the other orphans when renumbering.

## 13. Phase C of the referee revision: the maximal-factor argument

Responds to referee point 4, following `Report/Revision_Plan_verified.md` Phase C. Snapshot before
this phase: `backup-phaseC/`.

**What was wrong.** §2.4 asserted the existence of a maximal CSZ factor "by the line of reasoning of
[FKO, Prop. 7.26]" and never proved that CSZ factors are closed under suprema of chains — the step
that lets Zorn's lemma run. The proposition number could not be verified here, and the referee
believes it is wrong. The maximality contradiction itself was described in two bullet points rather
than proved. There was also a mismatch, not raised by the referee, between the paper's definitions
and those of the source it relies on for the dichotomy; see below.

**C1 — Lemma 2.26 (chains), with proof.** For a non-empty chain `{D_α}` of CSZ factors, the
σ-algebra generated by the union is CSZ. Given `E` in it, approximate `1_E` by `g = E(1_E | D_α)` —
the approximation is proved by a monotone-class argument, as in Moreira's Lemma 8.1.5 — and let
`H = {g > 1 − κ}` with `κ = 1/(2(t+1))`. A conditional Bonferroni inequality gives

        m(E ∩ T^{−d}E ∩ ⋯ ∩ T^{−td}E) ≥ ½ · m(H ∩ T^{−d}H ∩ ⋯ ∩ T^{−td}H)     for every d ∈ Z.   (2.27)

Because (2.27) holds for each step `d` separately, it passes through the uniform averages, the
quantification over all Cantor sets, and the dilations unchanged; that is all the adaptation from
Szemerédi's setting amounts to, and the text now says so. Neither separability nor ergodicity is used.

**C2 — the maximality argument, written out.** The proof of Theorem 2.21 is now a proof: the set of
CSZ factors is non-empty (the trivial factor) and has upper bounds for non-empty chains (Lemma 2.26);
take a maximal `D` by Zorn; if `D ≠ A`, the dichotomy (now Lemma 2.28) gives either that `A` is a
weakly mixing extension of `D`, so CSZ by (W), or a strictly larger compact extension, CSZ by (K).
Either contradicts maximality.

**Definitions, aligned with the dichotomy's source.** The dichotomy is cited to Furstenberg and, for
a proof in this language, to Moreira's Proposition 8.6.1. Checking his definitions against ours
showed two mismatches:

- *Weak mixing extension.* Ours required every `f ∈ L²(E)` with `E(f|D) = 0` to be conditionally
  weakly mixing. Moreira's Definition 8.2.5 quantifies only over the Hilbert module `L²(E|D)` — so the
  dichotomy as he proves it did **not** deliver our notion, which asked for more. Ours now quantifies
  over the module, which is all §3 uses (it needs only bounded `f`). Moreira's notion is otherwise
  stronger than ours (every `g`, uniform Cesàro means), which is the direction the dichotomy needs.
- *Conditional compactness.* Ours used forward orbits `n ∈ N` and unrestricted approximants;
  Moreira's Definition 8.2.8 uses `n ∈ Z` and approximants in the module, and his Lemma 8.4.3 — our
  Lemma 5.7 — assumes that. Ours is now exactly his. Theorem 5.3 needs only the forward orbit, a
  subset, so nothing downstream changes.

The text after Lemma 2.28 records both comparisons, and that Moreira's proof of the dichotomy assumes
ergodicity and uses the disintegration over `D`, which is where separability enters.

**C3 — structure.** Lemma 2.25 is now two extension principles, (W) and (K), still numbered 2.25.
The trivial-factor remark says weakly mixing and compact systems are the special cases, and that
Theorem 5.1 is unused. The old outline — the two bullets, "the four cases", and the `Prop. 7.26`
citation — is gone; FKO is cited for the strategy without a proposition number. Lemma 2.22(1), which
Phase B left orphaned, is removed, and references to the renumbered parts updated: (2)→(1) in
Remark 5.18, (3)→(2) in §3.

**Checks.** Builds clean, no undefined references, 27 pages. Lemma 2.25 and Theorem 5.3 keep their
numbers. A sweep for "7.26", "four cases", "first point" and "second point" finds nothing.

## 14. Phase D of the referee revision: the reductions

Responds to referee point 4′ (undocumented ergodic and separability reductions), following
`Report/Revision_Plan_verified.md` Phase D. Snapshot before this phase: `backup-phaseD/`.

**What was wrong.** §2.2 imposed three "standard reductions" — invertible, Borel, ergodic — with a
one-line citation. For the CSZ property they are not quite standard: the conclusion is a positive
liminf over *all* intervals of indices, and the usual reduction to ergodic components is written for
limits, or for ordinary Cesàro liminfs. Moreira's §7.5, which carries it out for uniform limits,
remarks that Fatou's lemma would handle a liminf; but a uniform liminf ranges over a two-parameter
family of windows and is not a liminf along one sequence, so Fatou does not apply to it directly.
Separately, Theorem 2.21 said "separable" without saying what was used, or where.

**What changed.**

- **Standing assumption (§2.2).** The enumerated reductions are replaced by an explicit standing
  assumption for §§2–5: `T` invertible, `X` a compact metric space with its Borel σ-algebra.
  Ergodicity is assumed only where stated. Theorem 2.21 and the dichotomy (Lemma 2.28) now say
  "ergodic system satisfying the standing assumption" instead of "ergodic, separable and invertible";
  this is exactly the setting of Moreira's §8, which the dichotomy is cited from.
- **New §2.5, Proposition 2.31, with proof:** if every ergodic system under the standing assumption
  is CSZ, then every invertible system is. Two steps.
  1. *A compact metric model.* Instead of an abstract isomorphism theorem, the explicit symbolic
     model `x ↦ (1_A(T^n x))_{n∈Z}` in `{0,1}^Z` with the shift. It preserves every correlation
     `m(∩_s T^{−d_s}A)` exactly, (2.32).
  2. *Ergodic decomposition* (Moreira, Theorem 7.3.1). Choose a sequence of windows realizing the
     uniform liminf for `μ`, apply Fatou's lemma *along that sequence*, and note that a liminf along
     one sequence of windows is at least the uniform liminf for each ergodic component. That
     component liminf is positive on a set of positive measure. The text says why this, and not
     Fatou applied directly, is the right step.
- **Where the hypotheses are used,** now recorded at the end of §2.5. The compact metric structure:
  the ergodic decomposition, the disintegration behind the joining `λ` of Lemma 2.7 (hence §3), and
  the dichotomy. Not the chain lemma. Ergodicity: only the dichotomy. Lemmas 2.25 and 2.26 and
  Theorems 5.1 and 5.3 hold without it.
- **Lemma 2.7's preamble.** The disintegration is cited to Moreira's Theorem 7.2.1 (verified: any
  sub-σ-algebra, compact metric `X`), and the `R`-invariance of `λ` is now proved — via
  `E(a∘T | D) = E(a | D)∘T` and rectangles — rather than asserted.
- Theorem 2.21's link to Theorem 1.2 now goes through Proposition 2.31.

**Checks.** Builds clean, no undefined references, 29 pages. No remaining use of "separable".

## 15. Phase E of the referee revision: the Cantor input, made self-contained

Responds to referee point 5, following `Report/Revision_Plan_verified.md` Phase E. Snapshot before
this phase: `backup-phaseE/`.

**The issue.** All of §3 rests on Lemma 2.15, the uniform exponential-sum bound
`sup_M |E_{M≤n<M+L} e(β k_n)| → 0` for `β` outside the countable set `E_0`. It was quoted from the
first paper. The referee, reading the public version, found its proof ending with "an argument
analogous to (4.10)" rather than the endpoint bookkeeping that uniformity in `M` needs. The local
`FirstPaper-Oct2026` already has the full argument; the public version apparently does not.

**What changed.** Lemma 2.15 now has its own proof, specialised to one frequency, which is all this
paper uses. It is shorter than the two-frequency original:

1. *Reduction to `gcd(D) = 1`*, via `k_n = s·k′_n` for the digit set `D/s`.
2. *Digit average.* `ρ(θ) = E_{d∈D} e(dθ)` has `|ρ| = 1` only at integers when `gcd(D) = 1`.
3. *Products over blocks.* `E_{0≤j<δ^ℓ} e(β k_j) = ∏_{c<ℓ} ρ(b^c β)`, (2.17).
4. *Window split.* Complete blocks of length `δ^i` inside `[M,N)`, with at most `2δ^i` leftover
   indices, give `|E_{M≤n<N} e(β k_n)| ≤ |P_i(β)| + 2δ^i/(N−M)`, (2.18), with no dependence on
   `M` — the uniformity is visible in the inequality itself. The inner sum over blocks is bounded
   trivially; the original's exact identity is not needed.
5. *Limit of `P_ℓ`.* If `‖b^c β‖ ≥ η` infinitely often, infinitely many factors are `≤ 1−κ`.
   Otherwise `‖b^c β‖ → 0`, and the doubling step `‖b^{c+1}β‖ = b‖b^cβ‖` below `1/(2b)` forces `β` to
   be `b`-adic. With one frequency this replaces the original's `(b−1)α` argument.

The citation is now to §4 of the first paper rather than to "Lemma 4.5 and (4.8)", which are the
local version's numbers; the public version numbers the same display (4.6).

**Numerical check** (script in the session scratchpad, not in the project). For five digit sets —
`b = 3, D = {0,2}`; `b = 5, D = {0,1,3}`; `b = 10, D = {0,2,4,6,8}`; `b = 7, D = {0,3}`;
`b = 4, D = {0,1,3}`, so `gcd(D) ∈ {1,2,3}` — the reduction `k_n = s·k′_n` and the block identity
held exactly in every tested case; the product formula (2.17) matched to `5·10⁻¹³`; the window bound
(2.18) held in all 1,500 random windows; and for `β = √2` the supremum over starting points decayed
as `L` grew (e.g. 0.208 → 0.063 → 0.018 for `L` = 50, 400, 3000 with `b = 5, D = {0,1,3}`).

**Remaining first-paper dependencies.**

- Lemma 2.11(i)–(ii), the block identities `k_n = Σ d_{n_c} b^c` and `k_{δ^i n + j} = b^i k_n + k_j`,
  is on the main route and still quoted from the first paper's Prop. 2.2 without proof. It is
  elementary — a few lines — and could be proved here in Phase F if you want the Cantor-set side
  fully self-contained.
- Theorem 2.16, the non-uniform ergodic theorem along `C`, and its Remark, are now referenced
  nowhere: Phase A replaced its only use. Phase F candidate for removal, along with Lemma 2.11(iii).
- Lemma 2.12 (residue distribution) is used only as context for Lemma 2.14, which supports the
  off-route Theorem 5.1.

**Checks.** Builds clean, no undefined references.

## 16. Phase F of the referee revision: editorial pass

Following `Report/Revision_Plan_verified.md` Phase F, plus a proof of the block identities as you
asked. Snapshot before this phase: `backup-phaseF/`.

- **Lemma 2.10 (block identities) now has a proof.** For (i), `n ↦ Σ_c d_{n_c} b^c` is a bijection
  onto `C` — because `d_0 = 0`, leading zeros change nothing — and it is increasing, by comparing the
  highest differing digit, so it is the enumeration. Part (ii) follows from (i) by shifting base-`δ`
  digits. Both identities had already been checked computationally, by the referee and in Phase E.
  The unused parts are gone: the sum-of-digits statements and (iii).
- **Orphans removed:** the proposition listing equivalent forms of weak mixing; the old Lemma 2.12
  (residue distributions, quoted), whose content survives as attributed prose motivating Lemma 2.12
  (syndetic residues); and the old Theorem 2.16 (non-uniform ergodic theorem) with its remark.
  Nothing referred to any of them.
- **Notation:** §2.2 wrote the measure as `μ`, the rest of the paper `m`; now `m` throughout, except
  in Proposition 2.30, where `μ` is a different measure on the symbolic model.
- **§5 reordered.** The main-route result, compact extensions, is now Theorem 5.1 in §5.1; the
  root-of-unity theorem is Theorem 5.17 in a closing §5.2, marked as independent of the main proof.
- **Introduction.** The roadmap now describes the actual architecture: the three statements behind
  Theorem 1.2, the two Cantor-set inputs, the two places where the Cantor set constrains the
  argument, and the independence of §4. §2.4 is retitled "Structure of the proof", and §2 has a label.
- **Change log.** The top summary is rewritten for the current state, with a numbering table mapping
  the referee's numbers to the revised ones. The round-1 claim that Lemma 2.13 "upgrades the compact
  case" is marked superseded, as §7(b) and Summary item 3 were in Phase A.

**Checks.** Builds clean, no undefined references, 30 pages. A sweep for unreferenced labels finds
only equation labels and three standalone results — Corollary 4.2 and Remarks 1.7 and 1.8 — which
are kept on purpose.

**A correction about earlier checks.** `main.log` is Latin-1, and under this machine's UTF-8 locale
`grep` silently matches nothing in it: it missed a "Reference … undefined" line planted in a copy.
So every "no undefined references" in this record before this point — §§11–15 and the 16 October
sections — rests on a check that could not have failed. Real LaTeX errors were always caught,
because every build used `-halt-on-error` and its exit code was checked; undefined references and
citations do not stop a build. With `LC_ALL=C grep -a`, tested against a planted warning and a
planted overfull line, the final state has **no** LaTeX warnings and no package warnings. That
check also exposed:

- six overfull lines, up to 57pt, all in text written during these revisions — Lemma 2.6's proof,
  Theorem 2.20, three displays in Lemma 3.2's proof, and Theorem 4.3's statement. All fixed, by
  displaying a formula, splitting a long display, or rephrasing.
- an `amsrefs` warning from the first paper's entry, `journal = {arxiv}`. That entry now gives the
  identifier you supplied, `arXiv:2602.15292`, and renders in the same form as the Kra–Shalom entry.
  Its year is now 2026, not 2025: the identifier's `2602` means February 2026. Case
  protection was added where the references rendered "cantor", "ip", "markov" and "digits i", and
  the Kra–Shalom eprint now reads `arXiv:2506.17771`.

## 17. Audit against the checklists

Run on 17 October against the union of the "Final proof-audit checklist" in the action plan and
§6 of `Report/Revision_Plan_verified.md` — ten distinct checks. Each was checked against the
source, not against memory of writing it. **No mathematical error was found.** Five places
asserted something without saying why, or said it imprecisely; all five are fixed.

| # | Check | Verdict | Evidence, and fix if any |
|---|---|---|---|
| 1 | No absolute value moved across an average | Pass, after fix | Every place where a modulus meets an average or integral is either the triangle inequality in the right direction, or an equality justified by non-negativity stated beside it. **Fix:** in Lemma 3.2, Step 2, the spectral step compared a complex integral with a real bound; the modulus, and the reason it may be taken inside, are now written out. |
| 2 | van der Corput matches the quantity estimated | Pass | (3.12) bounds exactly `E_{1≤h≤H} |E_{M≤n<N−h}⟨u_{n+h},u_n⟩|`, the quantity in Lemma 2.28, with the same window and range of `h`. The hypotheses hold (`‖u_n‖ ≤ 1`, `H < N−M`), and the constants close (`4√2 + 14 < 20`). |
| 3 | Induction hypotheses quoted verbatim | Pass | (3.10) is Lemma 3.2's own conclusion for `t−1` functions under `T^{b^ℓ}`, re-indexed, with the shifts on the conditional expectations kept. In §4 the hypothesis (length `ℓ−1`, all minimal systems, all `h`) is exactly what is invoked. |
| 4 | Inner products on the right space, under an invariant measure | Pass, after fix | All of §3 is in `L²(X,m)` or `L²(λ)`, with `λ` invariant under `T×T`. **Fix:** the induction in Lemma 3.2 ranged over "measure preserving transformations"; it now says *invertible*, which the proof needs (`T^{−s₁k_n}`, and the joining). The transformations actually used, powers of `T`, are invertible. |
| 5 | Uniform limits visibly uniform | Pass | Every uniform statement shows the supremum over the starting index or uses the `N−M→∞` convention defined in §2.1. The ordinary limits are ordinary by design: the definitions of weak and conditional weak mixing, Wiener's lemma, Lemma 2.21(2), Fatou along a chosen sequence, and Remark 1.7. |
| 6 | Compact branch: pure point spectrum only | Pass, after fix | §2.2 says pure point and gives the irrational rotation. §5.1 uses no spectral input. Periodic approximation appears only in Theorem 5.17, under its hypothesis. **Fix:** compact functions were defined by forward orbits and conditional compactness by two-sided ones; both are now two-sided, so "a compact system is a compact extension of the trivial factor" is immediate. |
| 7 | Chain closure for the full CSZ definition | Pass | Lemma 2.25 fixes arbitrary `C`, `t ≥ 1`, `i ≥ 0` and `E`. The comparison (2.26) holds for every `d ∈ Z`, and the hypothesis on `D_α` is used with the same `(C, t, i)`. |
| 8 | Theorem 5.1: measurability and indexing | Pass, after fix | `S(F)`, each `E_q`, and the selector `a(u,·)` carry their reasons; `u ≥ 1 ⟹ n ≥ b^i > max F`; `ι(a_u) < δ^i`; one point of `V` per block. **Fix:** `Q(F) ∈ D` was asserted; it now says why — a countable intersection, as `C` has countably many finite subsets. |
| 9 | Reductions keep a strictly positive bound | Pass | Proposition 2.30: `Y_+` is measurable with positive measure; Fatou runs along one realising sequence; `ℓ(y) ≥ c(y) > 0` on `Y_+`. Where the standing assumption and ergodicity are used is recorded, and the claim that ergodicity enters only through the dichotomy checks. |
| 10 | Introduction, roadmap and change log match | Pass, after fix | Every result number cited in this log's summary matches the build; all 42 rows of the numbering table match; the sources contain no hard-coded result numbers. **Fix:** the roadmap omitted the reduction step; it now names Proposition 2.30. |

After the fixes the paper builds at 31 pages with no LaTeX or package warnings and no overfull lines.
The first fix briefly produced an overfull line, since split.

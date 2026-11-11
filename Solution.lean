module

public import CantorSzemeredi.Frozen.MainTheorem
public import CantorSzemeredi.Frozen.Syndetic
public import CantorSzemeredi.Frozen.Integers

/-!
# Solution: the three main theorems, proved

The statements of `Challenge.lean`, word for word, proved by the development's theorems
`CantorSzemeredi.cantor_szemeredi`, `CantorSzemeredi.cantor_szemeredi_syndetic` and
`CantorSzemeredi.cantor_szemeredi_integers` (in `CantorSzemeredi/Frozen/`), which have the same
statements. The definitions they use are imported from the development under the names the
challenge uses.
-/

@[expose] public section

open MeasureTheory

namespace CantorSzemeredi.Palomar

/-- **Theorem `t:CSZ`** (main theorem).  For a Cantor set `𝒞_{b,D}` with `0 ∈ D`, every `ℓ ≥ 1`, every
invertible measure preserving system `(X, 𝒜, m, T)` and every non-negative `f ∈ L^∞(X)` that is
not identically zero,
`liminf_{N-M→∞} 𝔼_{M ≤ n < N} ∫ ∏_{j=0}^{ℓ} T^{j kₙ} f dm > 0`.

The uniform liminf is written out: there are `c > 0` and `L` such that every average over an
interval of indices `[M, N)` of length at least `L` is at least `c`. -/
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
          ((N : ℝ) - M) :=
  CantorSzemeredi.cantor_szemeredi b D hb hDb hD2 hDb' hD0 ℓ hℓ m T hT f hf hf0 hfne

/-- **Corollary `c:syndetic`**.  Under the assumptions of Theorem `t:CSZ`, the set of indices
`{n ∈ ℕ₀ : ∫ ∏_{j=0}^{ℓ} T^{j kₙ} f dm > 0}` is syndetic: it meets every interval `[n₀, n₀ + L]`. -/
theorem cantor_szemeredi_syndetic
    (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hDb' : D.card < b) (hD0 : 0 ∈ D)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    {X : Type*} [MeasurableSpace X] (m : Measure X) [IsProbabilityMeasure m]
    (T : X ≃ᵐ X) (hT : MeasurePreserving T m m)
    (f : X → ℝ) (hf : MemLp f ⊤ m) (hf0 : 0 ≤ᵐ[m] f) (hfne : ¬ f =ᵐ[m] 0) :
    ∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧
      0 < ∫ x, ∏ j ∈ Finset.range (ℓ + 1), f ((⇑T)^[j * cantorEnum b D n] x) ∂m :=
  CantorSzemeredi.cantor_szemeredi_syndetic b D hb hDb hD2 hDb' hD0 ℓ hℓ m T hT f hf hf0 hfne

/-- **Theorem `t:CSZ-Integers`**.  For every `A ⊆ ℤ` with `d*(A) > 0`, the set of indices
`B = {n ∈ ℕ : d*(A ∩ (A - kₙ) ∩ ⋯ ∩ (A - ℓ kₙ)) > 0}` is syndetic; and for every `n ∈ B`,
`A` contains the non-degenerate `(ℓ+1)`-term progression `a, a + kₙ, …, a + ℓ kₙ` for some `a`.
Here `A ∩ (A - kₙ) ∩ ⋯ ∩ (A - ℓ kₙ) = {a : a + j kₙ ∈ A for 0 ≤ j ≤ ℓ}`. -/
theorem cantor_szemeredi_integers
    (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hDb' : D.card < b) (hD0 : 0 ∈ D)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (A : Set ℤ) (hA : 0 < upperBanachDensity A) :
    (∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧ 1 ≤ n ∧
      0 < upperBanachDensity {a : ℤ | ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A}) ∧
    ∀ n : ℕ, 1 ≤ n →
      0 < upperBanachDensity {a : ℤ | ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A} →
      0 < cantorEnum b D n ∧ ∃ a : ℤ, ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A :=
  CantorSzemeredi.cantor_szemeredi_integers b D hb hDb hD2 hDb' hD0 ℓ hℓ A hA

end CantorSzemeredi.Palomar

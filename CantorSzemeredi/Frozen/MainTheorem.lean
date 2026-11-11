-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import CantorSzemeredi.Frozen.CantorEnum
import CantorSzemeredi.Proof.MainTheorem

/-!
# Frozen: `CantorSzemeredi.cantor_szemeredi` (Theorem `t:CSZ`)

The statement exactly as the authors approved it, before any
proof was written. It is the only declaration in this file. Only the proof between the
`FROZEN_ANCHOR_PROOF` marker comments may change, and only to
`by exact CantorSzemeredi.Proof.cantor_szemeredi`.
-/

@[expose] public section

open MeasureTheory

namespace CantorSzemeredi

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
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact CantorSzemeredi.Proof.cantor_szemeredi
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end CantorSzemeredi
-- FROZEN_ANCHOR_SUFFIX_END

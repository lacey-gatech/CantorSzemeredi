-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import CantorSzemeredi.Frozen.CantorEnum
import CantorSzemeredi.Proof.Syndetic

/-!
# Frozen: `CantorSzemeredi.cantor_szemeredi_syndetic` (Corollary `c:syndetic`)

The statement exactly as the authors approved it, before any
proof was written. It is the only declaration in this file. Only the proof between the
`FROZEN_ANCHOR_PROOF` marker comments may change, and only to
`by exact CantorSzemeredi.Proof.cantor_szemeredi_syndetic`.
-/

@[expose] public section

open MeasureTheory

namespace CantorSzemeredi

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
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact CantorSzemeredi.Proof.cantor_szemeredi_syndetic
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end CantorSzemeredi
-- FROZEN_ANCHOR_SUFFIX_END

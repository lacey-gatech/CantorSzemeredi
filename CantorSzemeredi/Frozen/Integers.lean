-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import CantorSzemeredi.Frozen.CantorEnum
public import CantorSzemeredi.Frozen.UpperBanachDensity
import CantorSzemeredi.Proof.Integers

/-!
# Frozen: `CantorSzemeredi.cantor_szemeredi_integers` (Theorem `t:CSZ-Integers`)

The statement exactly as the authors approved it, before any
proof was written. It is the only declaration in this file. Only the proof between the
`FROZEN_ANCHOR_PROOF` marker comments may change, and only to
`by exact CantorSzemeredi.Proof.cantor_szemeredi_integers`.
-/

@[expose] public section

open MeasureTheory

namespace CantorSzemeredi

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
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact CantorSzemeredi.Proof.cantor_szemeredi_integers
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end CantorSzemeredi
-- FROZEN_ANCHOR_SUFFIX_END

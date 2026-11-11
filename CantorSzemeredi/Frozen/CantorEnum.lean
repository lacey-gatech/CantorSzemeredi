module

public import Mathlib
public import CantorSzemeredi.Frozen.CantorSet

/-!
# Frozen: `CantorSzemeredi.cantorEnum`

The definition exactly as the authors approved it. It is the
only declaration in this file, and it is not edited.
-/

@[expose] public section

open MeasureTheory

namespace CantorSzemeredi

/-- The increasing enumeration `𝒞_{b,D} = {k₀ < k₁ < k₂ < ⋯}` (so `cantorEnum b D n = kₙ`). -/
noncomputable def cantorEnum (b : ℕ) (D : Finset ℕ) (n : ℕ) : ℕ :=
  Nat.nth (· ∈ cantorSet b D) n

end CantorSzemeredi

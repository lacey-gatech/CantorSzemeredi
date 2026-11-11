module

public import Mathlib

/-!
# Frozen: `CantorSzemeredi.upperBanachDensity`

The definition exactly as the authors approved it. It is the
only declaration in this file, and it is not edited.
-/

@[expose] public section

open MeasureTheory

namespace CantorSzemeredi

/-- Upper Banach density, paper equation `e:banach`:
`d*(A) = limsup_{N-M→∞} |A ∩ [M,N)| / (N-M)`, written as `inf_L sup_{N-M ≥ L}`. -/
noncomputable def upperBanachDensity (A : Set ℤ) : ℝ :=
  ⨅ L : ℕ, ⨆ (M : ℤ) (N : ℤ) (_ : M + L ≤ N), ((A ∩ Set.Ico M N).ncard : ℝ) / ((N : ℝ) - M)

end CantorSzemeredi

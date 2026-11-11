module

public import Mathlib

/-!
# Frozen: `CantorSzemeredi.cantorSet`

The definition exactly as the authors approved it. It is the
only declaration in this file, and it is not edited.
-/

@[expose] public section

open MeasureTheory

namespace CantorSzemeredi

/-- The classical integer Cantor set `𝒞_{b,D}`, paper equation `e:Cantor`:
`{ ∑_{j=0}^{k} d_j b^j : k ∈ ℕ₀, d_j ∈ D }`. -/
def cantorSet (b : ℕ) (D : Finset ℕ) : Set ℕ :=
  {x | ∃ k : ℕ, ∃ d : ℕ → ℕ, (∀ j ≤ k, d j ∈ D) ∧ x = ∑ j ∈ Finset.range (k + 1), d j * b ^ j}

end CantorSzemeredi

/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Basic
import CantorSzemeredi.Dynamics.SymbolicModel

/-!
# Furstenberg correspondence principle

Blueprint: `blueprint/src/chapter/structure.tex`, Theorem `thm:furstenberg-correspondence`.

Given `A ⊆ ℤ` with positive upper Banach density, there exists an invertible measure preserving
system `(X, 𝒜, m, T)` and a measurable set `B` with `m(B) = d*(A)` such that for every finite
set of integers `R`, the upper Banach density of `⋂ r ∈ R, (A - r)` is at least
`m(⋂ r ∈ R, T^{-r} B)`.

The system is constructed as the symbolic model on `{0,1}^ℤ` with a weak limit of empirical
measures along windows realizing the density.
-/

namespace CantorSzemeredi

open MeasureTheory

/-- **Theorem `thm:furstenberg-correspondence`** (Furstenberg correspondence principle).
If `A ⊆ ℤ` has positive upper Banach density `d*(A) > 0`, then there exists an MPS `S` and
a measurable set `B` with `m(B) = d*(A)` such that for every finite collection of integers `R`,
`d*(⋂ r ∈ R, (A - r)) ≥ m(⋂ r ∈ R, T^{-r} B)`.

Instantiate with `R = {0, r₁, …, rⱼ}` to recover the classical form
`d*(A ∩ (A - r₁) ∩ ⋯ ∩ (A - rⱼ)) ≥ m(B ∩ T^{-r₁}B ∩ ⋯ ∩ T^{-rⱼ}B)`. -/
theorem furstenberg_correspondence (A : Set ℤ) (hA : 0 < upperBanachDensity A) :
    ∃ (S : MPS) (B : Set S.X),
      MeasurableSet B ∧
      (S.m B).toReal = upperBanachDensity A ∧
      ∀ (R : Finset ℤ),
        upperBanachDensity (⋂ r ∈ R, (· + r) ⁻¹' A) ≥
          (S.m (⋂ r ∈ R, S.iter r ⁻¹' B)).toReal := by
  sorry

end CantorSzemeredi

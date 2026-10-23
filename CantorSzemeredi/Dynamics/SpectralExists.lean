/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.Spectral

/-!
# Existence of the spectral measure

Blueprint: the "Mathlib gap" remark after `def:spectral-measure`.

The route is the one recorded there: the continuous functional calculus turns
`f ↦ Re ⟪v, f(U) v⟫` into a positive linear functional on `C(𝕋, ℝ)`, and the
Riesz–Markov–Kakutani theorem represents it by a measure.

## Obstacles met on the way

* Mathlib's `cfc_nonneg` is stated for a scalar ring with an order, and **`ℂ` carries no `LE`
  instance**, so it is unavailable for the `ℂ`-valued calculus of a normal operator.
  Positivity is instead obtained by factoring: a non-negative `f` on the spectrum is
  `conj g * g` for `g = √f`, and `star x * x ≥ 0` holds in any C⋆-algebra.
* `cfc` takes functions `ℂ → ℂ`, so a function on `𝕋` must be transported to `ℂ`.  Rather than
  extending off the circle, we use `cfcHom`, which consumes `C(spectrum ℂ a, ℂ)` directly.
-/

namespace CantorSzemeredi

open MeasureTheory Complex ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator underlying a unitary equivalence. -/
noncomputable abbrev op (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H := U

theorem star_op (U : H ≃ₗᵢ[ℂ] H) : star (op U) = (U.symm : H →L[ℂ] H) :=
  U.adjoint_eq_symm

theorem op_mem_unitary (U : H ≃ₗᵢ[ℂ] H) : op U ∈ unitary (H →L[ℂ] H) := by
  constructor <;> rw [star_op] <;> ext x <;> simp

instance isStarNormal_op (U : H ≃ₗᵢ[ℂ] H) : IsStarNormal (op U) := by
  constructor
  change star (op U) * op U = op U * star (op U)
  rw [star_op]
  ext x
  simp

/-- The spectrum of a unitary lies on the unit circle. -/
theorem norm_eq_one_of_mem_spectrum (U : H ≃ₗᵢ[ℂ] H) {z : ℂ} (hz : z ∈ spectrum ℂ (op U)) :
    ‖z‖ = 1 := by
  have h := spectrum.subset_circle_of_unitary (𝕜 := ℂ) (op_mem_unitary U) hz
  exact mem_sphere_zero_iff_norm.1 h

/-! ### From the spectrum to the torus -/

/-- The spectrum of a unitary, viewed inside `Circle`. -/
noncomputable def specToCircle (U : H ≃ₗᵢ[ℂ] H) : C(spectrum ℂ (op U), Circle) where
  toFun z := ⟨(z : ℂ), by
    change (z : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    exact norm_eq_one_of_mem_spectrum U z.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val

/-- The spectrum of a unitary, viewed inside the torus `𝕋 = ℝ/ℤ`. -/
noncomputable def specToTorus (U : H ≃ₗᵢ[ℂ] H) : C(spectrum ℂ (op U), Torus) :=
  ⟨fun z => (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (specToCircle U z),
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous.comp
      (specToCircle U).continuous⟩

/-- Pulling a continuous function on the torus back to the spectrum. -/
noncomputable def pullback (U : H ≃ₗᵢ[ℂ] H) (f : C(Torus, ℝ)) :
    C(spectrum ℂ (op U), ℂ) :=
  ⟨fun z => ((f (specToTorus U z) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (f.continuous.comp (specToTorus U).continuous)⟩

@[simp] theorem pullback_apply (U : H ≃ₗᵢ[ℂ] H) (f : C(Torus, ℝ))
    (z : spectrum ℂ (op U)) : pullback U f z = ((f (specToTorus U z) : ℝ) : ℂ) := rfl

/-- The pullback is `ℝ`-linear in `f`. -/
theorem pullback_add (U : H ≃ₗᵢ[ℂ] H) (f g : C(Torus, ℝ)) :
    pullback U (f + g) = pullback U f + pullback U g := by
  ext z
  simp [pullback]

end CantorSzemeredi

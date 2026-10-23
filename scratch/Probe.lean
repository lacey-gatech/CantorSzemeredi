import Mathlib

open MeasureTheory Complex ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- the coercion `H ≃ₗᵢ[ℂ] H → H →L[ℂ] H` and its adjoint
example (U : H ≃ₗᵢ[ℂ] H) : adjoint (U : H →L[ℂ] H) = (U.symm : H →L[ℂ] H) :=
  U.adjoint_eq_symm

-- star is the adjoint
example (U : H ≃ₗᵢ[ℂ] H) : star (U : H →L[ℂ] H) = adjoint (U : H →L[ℂ] H) := rfl

-- the operator is star-normal
example (U : H ≃ₗᵢ[ℂ] H) : IsStarNormal (U : H →L[ℂ] H) := by
  constructor
  rw [Commute, SemiconjBy]
  show star (U : H →L[ℂ] H) * (U : H →L[ℂ] H) = (U : H →L[ℂ] H) * star (U : H →L[ℂ] H)
  rw [show star (U : H →L[ℂ] H) = (U.symm : H →L[ℂ] H) from U.adjoint_eq_symm]
  ext x
  simp

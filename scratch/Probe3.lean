import Mathlib

open MeasureTheory Complex ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- packaging as a unitary element, and the spectrum
example (U : H ≃ₗᵢ[ℂ] H) : (U : H →L[ℂ] H) ∈ unitary (H →L[ℂ] H) := by
  constructor
  · rw [show star (U : H →L[ℂ] H) = (U.symm : H →L[ℂ] H) from U.adjoint_eq_symm]
    ext x; simp
  · rw [show star (U : H →L[ℂ] H) = (U.symm : H →L[ℂ] H) from U.adjoint_eq_symm]
    ext x; simp

-- cfc basics
example (a : H →L[ℂ] H) [IsStarNormal a] : cfc (id : ℂ → ℂ) a = a := by exact?

example (a : H →L[ℂ] H) [IsStarNormal a] (f g : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) (hg : ContinuousOn g (spectrum ℂ a)) :
    cfc (fun z => f z * g z) a = cfc f a * cfc g a := by exact?

example (a : H →L[ℂ] H) [IsStarNormal a] (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) :
    cfc (fun z => starRingEnd ℂ (f z)) a = star (cfc f a) := by exact?

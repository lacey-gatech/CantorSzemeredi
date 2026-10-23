import CantorSzemeredi.Dynamics.SpectralExists

open MeasureTheory Complex ContinuousLinearMap CantorSzemeredi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- cfcHom is a star-algebra hom; is it ℝ-linear in the obvious sense on real-valued inputs?
example (U : H ≃ₗᵢ[ℂ] H) (f g : C(spectrum ℂ (op U), ℂ)) :
    cfcHom (isStarNormal_op U) (f + g)
      = cfcHom (isStarNormal_op U) f + cfcHom (isStarNormal_op U) g := by
  exact?

-- the factorisation route to positivity
example (A : H →L[ℂ] H) : 0 ≤ star A * A := by exact?

-- inner product against a positive operator
example (A : H →L[ℂ] H) (h : 0 ≤ A) (v : H) : 0 ≤ RCLike.re (inner ℂ (A v) v) := by
  have := ContinuousLinearMap.nonneg_iff_isPositive.mp h
  exact?

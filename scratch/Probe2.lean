import Mathlib

open MeasureTheory Complex ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- (f) spectrum of a unitary sits in the circle
example (U : H ≃ₗᵢ[ℂ] H) (z : ℂ) (hz : z ∈ spectrum ℂ (U : H →L[ℂ] H)) : ‖z‖ = 1 := by
  exact?

-- (d) the C*-order agrees with IsPositive
example (A : H →L[ℂ] H) (h : 0 ≤ A) : A.IsPositive := by
  exact?

-- (c) cfc over ℂ: a nonneg real function gives a nonneg operator
example (U : H ≃ₗᵢ[ℂ] H) (f : ℂ → ℂ) (hf : ∀ z ∈ spectrum ℂ (U : H →L[ℂ] H), 0 ≤ f z) :
    0 ≤ cfc f (U : H →L[ℂ] H) := by
  exact?

-- (e) powers
example (U : H ≃ₗᵢ[ℂ] H) (n : ℕ) :
    cfc (fun z : ℂ => z ^ n) (U : H →L[ℂ] H) = (U : H →L[ℂ] H) ^ n := by
  exact?

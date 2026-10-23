import CantorSzemeredi.Dynamics.SpectralExists

open MeasureTheory CantorSzemeredi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (U : H ≃ₗᵢ[ℂ] H) (v : H) : IsFiniteMeasure (specMeasure U v) := by
  rw [specMeasure]
  infer_instance

/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMLimit

/-!
# The conditional correlation function `φ`

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `eq:phipsi`.  For `v ∈ ℕ`,
`φ(v) = ∫ |⟨T^v f, f⟩_D| dm`, where `⟨·,·⟩_D` is the conditional inner product.  The last step of
the per-shift estimate identifies the bound `∫ |Exp(F_{j0}|D)|` with `φ(s_{j0} Δ_c)`, where
`F_{j0} = f · T^{s_{j0}Δ} f`.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Filter Topology

namespace MPS

/-- The blueprint's `φ(v) = ∫ |⟨T^v f, f⟩_D| dm`, with the conditional inner product of
`T^v f` and `f` over the factor `D`. -/
noncomputable def phiCorr (S : MPS.{0}) (D : Factor S) (f : S.X → ℝ) (v : ℕ) : ℝ :=
  ∫ x, |condInner D (f ∘ S.T^[v]) f x| ∂S.m

/-- The conditional expectation of the product `f · T^v f` is the conditional inner product
`⟨T^v f, f⟩_D`, so the integral of its modulus is `φ(v)`. -/
theorem integral_abs_condExp_mul_shift (S : MPS.{0}) (D : Factor S) (f : S.X → ℝ) (v : ℕ) :
    ∫ x, |S.m[(fun y => f y * f (S.T^[v] y)) | D.σ] x| ∂S.m = phiCorr S D f v := by
  have hfun : (fun y => f y * f (S.T^[v] y)) = (f ∘ S.T^[v]) * f := by
    funext y
    simp only [Pi.mul_apply, Function.comp_apply]
    ring
  unfold phiCorr
  rw [hfun]
  rfl

/-- The factor `F_j = f_j · T^{s_j D} f_j` of the correlation identity: the integral of the modulus
of its conditional expectation is `φ(s_j D)` for the factor `f_j`. -/
theorem integral_abs_condExp_factor (S : MPS.{0}) (D : Factor S) (s : ℕ → ℕ) (f : ℕ → S.X → ℝ)
    (Δ j : ℕ) :
    ∫ x, |S.m[(fun y => f j y * f j (S.T^[s j * Δ] y)) | D.σ] x| ∂S.m
      = phiCorr S D (f j) (s j * Δ) :=
  integral_abs_condExp_mul_shift S D (f j) (s j * Δ)

end MPS

end CantorSzemeredi

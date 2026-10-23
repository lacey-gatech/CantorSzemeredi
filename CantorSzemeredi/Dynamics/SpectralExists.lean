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

open MeasureTheory Complex ContinuousLinearMap CompactlySupportedContinuousMap

open scoped CompactlySupported

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

/-- The torus coordinate of a spectral point recovers that point: `e(α) = z`. -/
theorem fourier_specToTorus (U : H ≃ₗᵢ[ℂ] H) (z : spectrum ℂ (op U)) :
    fourier 1 (specToTorus U z) = (z : ℂ) := by
  rw [fourier_one, specToTorus]
  change ((AddCircle.toCircle
    ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (specToCircle U z))) : ℂ)
      = (z : ℂ)
  rw [← AddCircle.homeomorphCircle_apply (T := (1 : ℝ)) one_ne_zero]
  rw [Homeomorph.apply_symm_apply]
  rfl

/-! ### The positive linear functional -/

variable (U : H ≃ₗᵢ[ℂ] H) (v : H)

/-- The functional `f ↦ Re ⟪f(U) v, v⟫` on `C(𝕋, ℝ)`, built through the continuous functional
calculus. -/
noncomputable def specFun (f : C(Torus, ℝ)) : ℝ :=
  RCLike.re (inner ℂ ((cfcHom (isStarNormal_op U) (pullback U f)) v) v)

theorem specFun_congr {f g : C(Torus, ℝ)} (h : ∀ α, f α = g α) :
    specFun U v f = specFun U v g := by
  have hfg : f = g := by ext α; exact h α
  rw [hfg]

theorem specFun_add (f g : C(Torus, ℝ)) :
    specFun U v (f + g) = specFun U v f + specFun U v g := by
  rw [specFun, specFun, specFun, pullback_add, map_add]
  simp

theorem pullback_smul (c : ℝ) (f : C(Torus, ℝ)) :
    pullback U (c • f) = (c : ℂ) • pullback U f := by
  ext z
  simp [pullback]

theorem specFun_smul (c : ℝ) (f : C(Torus, ℝ)) :
    specFun U v (c • f) = c * specFun U v f := by
  rw [specFun, specFun, pullback_smul, map_smul]
  simp

/-- **Positivity.**  `cfc_nonneg` is unavailable here (`ℂ` has no order), so a non-negative `f`
is factored as `conj g * g` with `g = √f`, and `star x * x ≥ 0` in any C⋆-algebra. -/
theorem specFun_nonneg {f : C(Torus, ℝ)} (hf : ∀ α, 0 ≤ f α) : 0 ≤ specFun U v f := by
  -- The square root of `f`, pulled back to the spectrum.
  set g : C(spectrum ℂ (op U), ℂ) :=
    ⟨fun z => ((Real.sqrt (f (specToTorus U z)) : ℝ) : ℂ),
      Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
        (f.continuous.comp (specToTorus U).continuous))⟩ with hgdef
  have hfac : pullback U f = star g * g := by
    ext z
    simp only [pullback_apply, hgdef, ContinuousMap.mul_apply, ContinuousMap.star_apply,
      ContinuousMap.coe_mk, RCLike.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hf _)]
  have hnn : 0 ≤ cfcHom (isStarNormal_op U) (pullback U f) := by
    rw [hfac, map_mul, map_star]
    exact star_mul_self_nonneg _
  exact IsPositive.re_inner_nonneg_left
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hnn) v

/-- The functional as a bundled positive linear map on compactly supported functions, which is
what the Riesz–Markov–Kakutani theorem consumes.  On the compact space `𝕋` every continuous
function is compactly supported. -/
noncomputable def specPLM : C_c(Torus, ℝ) →ₚ[ℝ] ℝ where
  toFun f := specFun U v ⟨⇑f, map_continuous f⟩
  map_add' f g := by
    have h1 : specFun U v ⟨⇑(f + g), map_continuous (f + g)⟩
        = specFun U v (⟨⇑f, map_continuous f⟩ + ⟨⇑g, map_continuous g⟩) :=
      specFun_congr U v fun α => by simp
    rw [h1]
    exact specFun_add U v _ _
  map_smul' c f := by
    have h1 : specFun U v ⟨⇑(c • f), map_continuous (c • f)⟩
        = specFun U v (c • (⟨⇑f, map_continuous f⟩ : C(Torus, ℝ))) :=
      specFun_congr U v fun α => by simp
    rw [h1]
    simpa using specFun_smul U v c _
  monotone' := by
    intro f g hfg
    have hdiff : 0 ≤ specFun U v
        ((⟨⇑g, map_continuous g⟩ : C(Torus, ℝ)) - ⟨⇑f, map_continuous f⟩) := by
      refine specFun_nonneg U v fun α => ?_
      simpa using hfg α
    have hsub : specFun U v ((⟨⇑g, map_continuous g⟩ : C(Torus, ℝ)) - ⟨⇑f, map_continuous f⟩)
        = specFun U v ⟨⇑g, map_continuous g⟩ - specFun U v ⟨⇑f, map_continuous f⟩ := by
      have h := specFun_add U v
        ((⟨⇑g, map_continuous g⟩ : C(Torus, ℝ)) - ⟨⇑f, map_continuous f⟩)
        ⟨⇑f, map_continuous f⟩
      simp only [sub_add_cancel] at h
      linarith
    rw [hsub] at hdiff
    linarith

/-! ### The measure -/

/-- The measure representing `specFun`, from the Riesz–Markov–Kakutani theorem. -/
noncomputable def specMeasure : Measure Torus := RealRMK.rieszMeasure (specPLM U v)

/-- **The representation.**  `∫ f dσ = Re ⟪f(U) v, v⟫` for every continuous `f : 𝕋 → ℝ`. -/
theorem integral_specMeasure (f : C(Torus, ℝ)) :
    ∫ α, f α ∂(specMeasure U v) = specFun U v f := by
  have h := RealRMK.integral_rieszMeasure (specPLM U v)
    (CompactlySupportedContinuousMap.continuousMapEquiv f)
  rw [specMeasure]
  refine h.trans ?_
  change specFun U v ⟨⇑(CompactlySupportedContinuousMap.continuousMapEquiv f), _⟩ = specFun U v f
  exact specFun_congr U v fun α => rfl

end CantorSzemeredi

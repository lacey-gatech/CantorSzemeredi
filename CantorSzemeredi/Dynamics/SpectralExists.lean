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
  RCLike.re (inner ℂ v ((cfcHom (isStarNormal_op U) (pullback U f)) v))

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
  exact IsPositive.re_inner_nonneg_right
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

/-! ### Matching `z ↦ zⁿ` with `Uⁿ` -/

omit [CompleteSpace H] in
theorem op_mul (U V : H ≃ₗᵢ[ℂ] H) : op (U * V) = op U * op V :=
  ContinuousLinearMap.ext (congrFun rfl)

omit [CompleteSpace H] in
theorem op_one : op (1 : H ≃ₗᵢ[ℂ] H) = (1 : H →L[ℂ] H) :=
  ContinuousLinearMap.ext (congrFun rfl)

omit [CompleteSpace H] in
theorem op_pow (U : H ≃ₗᵢ[ℂ] H) (m : ℕ) : op (U ^ m) = (op U) ^ m := by
  induction m with
  | zero => simpa using op_one
  | succ m ih => rw [pow_succ, pow_succ, op_mul, ih]

theorem op_inv (U : H ≃ₗᵢ[ℂ] H) : op U⁻¹ = star (op U) := by
  rw [star_op]
  rfl

set_option linter.deprecated false in
/-- `z ↦ zⁿ` as a continuous function on the spectrum of a unitary.

`Set.restrict` is used rather than the newer `Set.domRestrict`: the latter does not give the
definitional unfolding that `zpowSpec_apply` and the `cfcHom` lemmas below rely on. -/
noncomputable def zpowSpec (U : H ≃ₗᵢ[ℂ] H) (n : ℤ) : C(spectrum ℂ (op U), ℂ) :=
  ⟨Set.restrict _ (fun z : ℂ => z ^ n),
    ContinuousOn.restrict ((continuousOn_zpow₀ n).mono (by
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hzero
      have := norm_eq_one_of_mem_spectrum U hz
      rw [hzero] at this
      simp at this))⟩

@[simp] theorem zpowSpec_apply (U : H ≃ₗᵢ[ℂ] H) (n : ℤ) (z : spectrum ℂ (op U)) :
    zpowSpec U n z = (z : ℂ) ^ n := rfl

/-- `zpowSpec U 1` is the restriction of the identity, which `cfcHom` sends to `U`. -/
theorem cfcHom_zpowSpec_one (U : H ≃ₗᵢ[ℂ] H) :
    cfcHom (isStarNormal_op U) (zpowSpec U 1) = op U := by
  rw [show zpowSpec U 1
      = ContinuousMap.restrict (spectrum ℂ (op U)) (ContinuousMap.id ℂ) by
    ext z; simp]
  exact cfcHom_id (isStarNormal_op U)

/-- The star of the identity restriction is `z ↦ z⁻¹` on the spectrum, since `|z| = 1`. -/
theorem zpowSpec_neg_one (U : H ≃ₗᵢ[ℂ] H) :
    zpowSpec U (-1) = star (zpowSpec U 1) := by
  ext z
  simp only [zpowSpec_apply, ContinuousMap.star_apply, RCLike.star_def]
  have hz : ‖(z : ℂ)‖ = 1 := norm_eq_one_of_mem_spectrum U z.2
  have hne : (z : ℂ) ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  rw [zpow_neg, zpow_one, Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
  simp

theorem zpowSpec_mul (U : H ≃ₗᵢ[ℂ] H) (m n : ℤ) :
    zpowSpec U (m + n) = zpowSpec U m * zpowSpec U n := by
  ext z
  have hne : (z : ℂ) ≠ 0 := by
    intro h
    have hz := norm_eq_one_of_mem_spectrum U z.2
    rw [h] at hz
    simp at hz
  simp [zpow_add₀ hne]

/-- **`cfcHom` carries `z ↦ zⁿ` to `Uⁿ`.** -/
theorem cfcHom_zpowSpec (U : H ≃ₗᵢ[ℂ] H) (n : ℤ) :
    cfcHom (isStarNormal_op U) (zpowSpec U n) = op (U ^ n) := by
  induction n using Int.induction_on with
  | zero => simpa [show zpowSpec U 0 = 1 by ext z; simp] using op_one.symm
  | succ m ih =>
    rw [zpowSpec_mul, map_mul, ih, cfcHom_zpowSpec_one,
      show (U ^ ((m : ℤ) + 1)) = U ^ (m : ℤ) * U from zpow_add_one U m, op_mul]
  | pred m ih =>
    rw [show (-(m : ℤ) - 1) = (-(m : ℤ)) + (-1) by ring, zpowSpec_mul, map_mul, ih,
      zpowSpec_neg_one, map_star, cfcHom_zpowSpec_one,
      show (U ^ (-(m : ℤ) + -1)) = (U ^ (-(m : ℤ))) * U⁻¹ by
        rw [zpow_add U (-(m : ℤ)) (-1), zpow_neg_one],
      op_mul, op_inv]

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

/-! ### The Fourier coefficients

Splitting `fourier n` into real and imaginary parts, each a continuous real function on `𝕋`,
and recombining: the pullbacks add up to `zpowSpec U n`, which `cfcHom` sends to `Uⁿ`.
-/

/-- The real part of a character, as a continuous real function on the torus. -/
noncomputable def fourierRe (n : ℤ) : C(Torus, ℝ) :=
  ⟨fun α => (fourier n α).re, Complex.continuous_re.comp (fourier n).continuous⟩

/-- The imaginary part of a character. -/
noncomputable def fourierIm (n : ℤ) : C(Torus, ℝ) :=
  ⟨fun α => (fourier n α).im, Complex.continuous_im.comp (fourier n).continuous⟩

/-- The two pullbacks recombine to `z ↦ zⁿ` on the spectrum. -/
theorem pullback_fourier (U : H ≃ₗᵢ[ℂ] H) (n : ℤ) :
    pullback U (fourierRe n) + Complex.I • pullback U (fourierIm n) = zpowSpec U n := by
  ext z
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, pullback_apply,
    zpowSpec_apply, smul_eq_mul, fourierRe, fourierIm, ContinuousMap.coe_mk]
  have h1 : fourier n (specToTorus U z) = (fourier 1 (specToTorus U z)) ^ n :=
    fourier_eq_zpow n _
  have hz : fourier n (specToTorus U z) = (z : ℂ) ^ n := by
    rw [h1, fourier_specToTorus]
  rw [← hz, mul_comm Complex.I]
  exact Complex.re_add_im _

/-- A self-adjoint operator has real inner products against a single vector. -/
theorem inner_self_real {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (v : H) :
    (inner ℂ v (A v) : ℂ) = ((RCLike.re (inner ℂ v (A v)) : ℝ) : ℂ) := by
  have hsym : (inner ℂ (A v) v : ℂ) = inner ℂ v (A v) := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hA.adjoint_eq]
  have hconj : (starRingEnd ℂ) (inner ℂ v (A v)) = inner ℂ v (A v) := by
    rw [← hsym]
    rw [inner_conj_symm (𝕜 := ℂ) v (A v)]
    exact hsym.symm
  exact (Complex.conj_eq_iff_re.1 hconj).symm

/-- The pullback of a real function gives a self-adjoint operator. -/
theorem isSelfAdjoint_cfcHom_pullback (U : H ≃ₗᵢ[ℂ] H) (f : C(Torus, ℝ)) :
    IsSelfAdjoint (cfcHom (isStarNormal_op U) (pullback U f)) := by
  rw [IsSelfAdjoint, ← map_star]
  congr 1
  ext z
  simp [pullback, RCLike.star_def]

/-- `specFun` computes the inner product exactly, not merely its real part. -/
theorem inner_eq_specFun (U : H ≃ₗᵢ[ℂ] H) (v : H) (f : C(Torus, ℝ)) :
    (inner ℂ v ((cfcHom (isStarNormal_op U) (pullback U f)) v) : ℂ)
      = ((specFun U v f : ℝ) : ℂ) :=
  inner_self_real (isSelfAdjoint_cfcHom_pullback U f) v

/-- **Existence of the spectral measure.**  For every unitary `U` on a complex Hilbert space
and every vector `v`, the measure produced by Riesz–Markov–Kakutani from the functional
`f ↦ Re ⟪v, f(U) v⟫` is a spectral measure for `U` at `v`. -/
theorem hasSpectralMeasure_specMeasure (U : H ≃ₗᵢ[ℂ] H) (v : H) :
    HasSpectralMeasure U v (specMeasure U v) where
  isFinite := by rw [specMeasure]; infer_instance
  inner_eq n := by
    have hfin : IsFiniteMeasure (specMeasure U v) := by rw [specMeasure]; infer_instance
    -- Integrability of the two real parts.
    have hint : ∀ f : C(Torus, ℝ), Integrable (fun α => f α) (specMeasure U v) := by
      intro f
      refine MemLp.integrable (q := ⊤) le_top ?_
      obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support
        (HasCompactSupport.of_compactSpace f)
      exact memLp_top_of_bound f.continuous.aestronglyMeasurable C
        (Filter.Eventually.of_forall hC)
    -- Split the complex integral into real and imaginary parts.
    have hfourint : Integrable (fun α => fourier n α) (specMeasure U v) := by
      refine MemLp.integrable (q := ⊤) le_top ?_
      refine memLp_top_of_bound (fourier n).continuous.aestronglyMeasurable 1 ?_
      filter_upwards with α
      rw [fourier_apply]
      exact le_of_eq (Circle.norm_coe _)
    have hsplit : ∫ α, fourier n α ∂(specMeasure U v)
        = ((∫ α, fourierRe n α ∂(specMeasure U v) : ℝ) : ℂ)
          + Complex.I * ((∫ α, fourierIm n α ∂(specMeasure U v) : ℝ) : ℂ) := by
      rw [← integral_re_add_im hfourint, mul_comm Complex.I]
      rfl
    rw [hsplit, integral_specMeasure, integral_specMeasure]
    -- Recombine the two pullbacks into `z ↦ zⁿ`.
    have hcomb : ((specFun U v (fourierRe n) : ℝ) : ℂ)
        + Complex.I * ((specFun U v (fourierIm n) : ℝ) : ℂ)
        = inner ℂ v ((cfcHom (isStarNormal_op U) (zpowSpec U n)) v) := by
      rw [← pullback_fourier U n, map_add, map_smul]
      rw [← inner_eq_specFun U v (fourierRe n), ← inner_eq_specFun U v (fourierIm n)]
      simp
    rw [hcomb, cfcHom_zpowSpec]
    rfl

end CantorSzemeredi

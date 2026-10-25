/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.Koopman
import CantorSzemeredi.Dynamics.Spectral
import CantorSzemeredi.Cantor.Spectral

/-!
# The uniform ergodic theorem along a Cantor set

Blueprint: `blueprint/src/chapter/cantor.tex`, `cor:uniform-ergodic`.

If `f ∈ L²` has atomless spectral measure `σ_f` and `s ≥ 1`, then the uniform averages
`‖E_{M ≤ n < N} T^{s k_n} f‖₂` tend to `0` as `N - M → ∞`.  The spectral identity turns the
norm into an integral of an exponential sum, which is bounded by `Φ_{N-M}(s α)`, and
`lem:uniform-spectral` gives the limit.
-/

namespace CantorSzemeredi

open MeasureTheory Filter Topology Complex

namespace MPS

variable {S : MPS}

/-- The Fourier character on the circle, evaluated on a representative, is the exponential `e`. -/
theorem fourier_int_coe_eq (m : ℤ) (x : ℝ) :
    fourier m (x : AddCircle (1 : ℝ)) = e ((m : ℝ) * x) := by
  rw [fourier_coe_apply]
  unfold e
  congr 1
  push_cast
  ring

/-- The uniform averages of a window of length `L` are bounded by `Φ_L`. -/
theorem window_avg_le_Phi (C : CantorData) (β : ℝ) (M L : ℕ) (hL : 0 < L) :
    ‖(L : ℂ)⁻¹ * ∑ n ∈ Finset.Ico M (M + L), e (β * C.enum n)‖ ≤ C.Phi L β := by
  have hbdd : BddAbove (Set.range fun M' : ℕ =>
      ‖(L : ℂ)⁻¹ * ∑ n ∈ Finset.Ico M' (M' + L), e (β * C.enum n)‖) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨M', rfl⟩
    show ‖(L : ℂ)⁻¹ * ∑ n ∈ Finset.Ico M' (M' + L), e (β * C.enum n)‖ ≤ 1
    have hsum := C.norm_sum_Ico_le_card β M' (M' + L)
    have hcard : ((M' + L - M' : ℕ) : ℝ) = (L : ℝ) := by
      congr 1
      simp
    rw [hcard] at hsum
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (L : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ico M' (M' + L), e (β * C.enum n)‖
        ≤ (L : ℝ)⁻¹ * L := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := by field_simp
  exact le_ciSup hbdd M

/-- The length of a uniform window tends to infinity along `uniformFilter`. -/
theorem tendsto_uniform_length :
    Tendsto (fun p : ℕ × ℕ => p.2 - p.1) uniformFilter atTop :=
  Filter.tendsto_atTop.2 fun b => mem_uniformFilter_iff.2 ⟨b, fun _ _ h => h⟩

/-- **Corollary `cor:uniform-ergodic`.**  If `v ∈ L²` has atomless spectral measure `σ` and
`s ≥ 1`, then the uniform averages of `U^{s k_n} v` tend to `0` in norm as `N - M → ∞`. -/
theorem tendsto_uniformAvg_koopman_zero (C : CantorData) {s : ℕ} (hs : 1 ≤ s)
    {v : Lp ℂ 2 S.m} {σ : Measure Torus} (hσ : HasSpectralMeasure S.koopman v σ)
    [NullSingletonClass σ] :
    Tendsto (fun p : ℕ × ℕ => ‖((p.2 - p.1 : ℕ) : ℂ)⁻¹ •
        ∑ n ∈ Finset.Ico p.1 p.2, (S.koopman ^ ((s * C.enum n : ℕ) : ℤ)) v‖)
      uniformFilter (𝓝 0) := by
  haveI := hσ.isFinite
  set I : ℕ → ℝ := fun L => ∫ α, C.PhiCircle L (s • α) ∂σ with hI_def
  have hI0 : Tendsto I atTop (𝓝 0) := C.tendsto_integral_Phi_zero hs σ
  -- each window average has squared norm at most `I(N - M)`
  have hwin : ∀ M N : ℕ, 0 < N - M →
      ‖((N - M : ℕ) : ℂ)⁻¹ • ∑ n ∈ Finset.Ico M N, (S.koopman ^ ((s * C.enum n : ℕ) : ℤ)) v‖ ^ 2
        ≤ I (N - M) := by
    intro M N hL'
    have hNM : N = M + (N - M) := by omega
    set L := N - M with hL_def
    rw [Finset.smul_sum, HasSpectralMeasure.norm_sum_sq hσ (Finset.Ico M N) (fun _ => ((L : ℕ) : ℂ)⁻¹)
      (fun n => ((s * C.enum n : ℕ) : ℤ))]
    have hpt : ∀ α : Torus,
        ‖∑ i ∈ Finset.Ico M N, ((L : ℕ) : ℂ)⁻¹ * fourier ((s * C.enum i : ℕ) : ℤ) α‖ ^ 2
          ≤ C.PhiCircle L (s • α) := by
      intro α
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective α
      have hcoe : ∑ i ∈ Finset.Ico M N, ((L : ℕ) : ℂ)⁻¹
            * fourier ((s * C.enum i : ℕ) : ℤ) (x : AddCircle (1 : ℝ))
          = ((L : ℕ) : ℂ)⁻¹ * ∑ n ∈ Finset.Ico M (M + L), e (((s : ℝ) * x) * C.enum n) := by
        rw [← hNM, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [fourier_int_coe_eq]
        congr 2
        push_cast
        ring
      rw [hcoe, coe_nsmul_addCircle, C.PhiCircle_coe]
      have hbound := window_avg_le_Phi C ((s : ℝ) * x) M L hL'
      have hnn : 0 ≤ ‖((L : ℕ) : ℂ)⁻¹ * ∑ n ∈ Finset.Ico M (M + L),
          e (((s : ℝ) * x) * C.enum n)‖ := norm_nonneg _
      have hle1 : C.Phi L ((s : ℝ) * x) ≤ 1 := C.Phi_le_one L _
      nlinarith
    have hLHS_meas : Continuous fun α : Torus =>
        ‖∑ i ∈ Finset.Ico M N, ((L : ℕ) : ℂ)⁻¹ * fourier ((s * C.enum i : ℕ) : ℤ) α‖ ^ 2 := by
      refine Continuous.pow (Continuous.norm ?_) 2
      exact continuous_finset_sum _ fun i _ => continuous_const.mul (fourier _).continuous
    have hLHS_int : Integrable (fun α : Torus =>
        ‖∑ i ∈ Finset.Ico M N, ((L : ℕ) : ℂ)⁻¹ * fourier ((s * C.enum i : ℕ) : ℤ) α‖ ^ 2) σ := by
      refine (integrable_const (1 : ℝ)).mono' hLHS_meas.aestronglyMeasurable
        (ae_of_all _ fun α => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (hpt α).trans (C.PhiCircle_le_one L _)
    have hRHS_int : Integrable (fun α : Torus => C.PhiCircle L (s • α)) σ :=
      (integrable_const (1 : ℝ)).mono' (C.measurable_PhiCircle L |>.comp
          (measurable_nsmul_addCircle s)).aestronglyMeasurable
        (ae_of_all _ fun α => by
          rw [Real.norm_eq_abs, abs_of_nonneg (C.PhiCircle_nonneg L _)]
          exact C.PhiCircle_le_one L _)
    exact integral_mono hLHS_int hRHS_int hpt
  -- conclusion by squeezing
  have hsq : ∀ᶠ p : ℕ × ℕ in uniformFilter,
      ‖((p.2 - p.1 : ℕ) : ℂ)⁻¹ • ∑ n ∈ Finset.Ico p.1 p.2, (S.koopman ^ ((s * C.enum n : ℕ) : ℤ)) v‖
        ≤ Real.sqrt (I (p.2 - p.1)) := by
    filter_upwards [tendsto_uniform_length.eventually (eventually_ge_atTop 1)] with p hp
    have h2 := hwin p.1 p.2 (by omega)
    have hnn : 0 ≤ ‖((p.2 - p.1 : ℕ) : ℂ)⁻¹ • ∑ n ∈ Finset.Ico p.1 p.2,
        (S.koopman ^ ((s * C.enum n : ℕ) : ℤ)) v‖ := norm_nonneg _
    rw [← Real.sqrt_sq hnn]
    exact Real.sqrt_le_sqrt h2
  have hg : Tendsto (fun p : ℕ × ℕ => Real.sqrt (I (p.2 - p.1))) uniformFilter (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp (hI0.comp tendsto_uniform_length)
    rw [Real.sqrt_zero] at h
    exact h
  exact squeeze_zero' (Filter.Eventually.of_forall fun p => norm_nonneg _) hsq hg

end MPS

end CantorSzemeredi

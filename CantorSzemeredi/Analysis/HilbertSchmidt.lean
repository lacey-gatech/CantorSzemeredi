/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import Mathlib

/-!
# Integral operators with an `L²` kernel

Mathlib has `IsCompactOperator` but no theory of integral (Hilbert–Schmidt) operators: there
are no Schatten classes, and the only `Schmidt` in the library is Gram–Schmidt
orthogonalization.  This file supplies the first piece, written so that it could be upstreamed
as is.

For a kernel `k ∈ L²(μ ⊗ ν)` the integral operator

  `(T_k f) x = ∫ k (x, y) · f y ∂ν`

satisfies the **Hilbert–Schmidt bound**

  `‖T_k f‖_{L²(μ)} ≤ ‖k‖_{L²(μ⊗ν)} · ‖f‖_{L²(ν)}`,

which is `eLpNorm_integralKernel_le` below.  Everything is phrased with `eLpNorm`, valued in
`ℝ≥0∞`, so no integrability side conditions are needed: the bound holds unconditionally, and
is vacuous when the right-hand side is infinite.

## Why this file exists here

It is the missing input to the Hilbert–Schmidt step of the Furstenberg dichotomy
(`lem:dichotomy` of the blueprint): the eigenfunction produced by
`HasSpectralMeasure.exists_eigenvector_of_atom` has to be read as a kernel on the fibres of a
disintegration, and the operator it defines has to be compact.

## What is still missing

Compactness.  The standard route is that kernels of the form `∑ gᵢ(x) hᵢ(y)` are dense in
`L²(μ ⊗ ν)`, give finite-rank operators, and `isCompactOperator_of_tendsto` (which Mathlib
has) closes the argument.  The density step is the work.
-/

open MeasureTheory ENNReal

namespace HilbertSchmidt

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite ν]

/-- The integral operator attached to a kernel. -/
noncomputable def integralKernel (k : α × β → ℂ) (f : β → ℂ) : α → ℂ :=
  fun x => ∫ y, k (x, y) * f y ∂ν

omit [MeasurableSpace α] [SFinite ν] in
/-- The pointwise Cauchy–Schwarz bound: `|T_k f x| ≤ ‖k(x, ·)‖_{L²(ν)} ‖f‖_{L²(ν)}`. -/
theorem enorm_integralKernel_le (k : α × β → ℂ) (f : β → ℂ)
    (hk : ∀ x, AEMeasurable (fun y => ‖k (x, y)‖ₑ) ν) (hf : AEMeasurable (fun y => ‖f y‖ₑ) ν)
    (x : α) :
    ‖integralKernel (ν := ν) k f x‖ₑ
      ≤ (∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))
        * (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
  calc ‖integralKernel (ν := ν) k f x‖ₑ
      ≤ ∫⁻ y, ‖k (x, y) * f y‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y, ‖k (x, y)‖ₑ * ‖f y‖ₑ ∂ν := by
        refine lintegral_congr fun y => ?_
        rw [enorm_mul]
    _ ≤ (∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))
        * (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two (hk x) hf

private theorem eLpNorm_two_eq_rpow {γ : Type*} [MeasurableSpace γ] (ρ : Measure γ)
    (g : γ → ℂ) (hg : AEStronglyMeasurable g ρ) :
    eLpNorm g 2 ρ = (∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ) ∂ρ) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg]
  norm_num

/-- **The Hilbert–Schmidt bound.**  `‖T_k f‖_{L²(μ)} ≤ ‖k‖_{L²(μ⊗ν)} ‖f‖_{L²(ν)}`.

Stated with `eLpNorm`, so it holds unconditionally: no integrability hypotheses, and the
bound is vacuous when the right-hand side is infinite. -/
theorem eLpNorm_integralKernel_le {k : α × β → ℂ} {f : β → ℂ}
    (hk : AEStronglyMeasurable k (μ.prod ν))
    (hkx : ∀ x, AEMeasurable (fun y => k (x, y)) ν)
    (hf : AEStronglyMeasurable f ν)
    (hKf : AEStronglyMeasurable (integralKernel (ν := ν) k f) μ) :
    eLpNorm (integralKernel (ν := ν) k f) 2 μ
      ≤ eLpNorm k 2 (μ.prod ν) * eLpNorm f 2 ν := by
  -- Write all three `eLpNorm`s as `rpow`s of lintegrals.
  have htwo : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have htop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  set A : ℝ≥0∞ := (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) with hA
  -- Pointwise Cauchy–Schwarz, then integrate in `x`.
  have hptw : ∀ x, ‖integralKernel (ν := ν) k f x‖ₑ ^ (2 : ℝ)
      ≤ (∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ) ∂ν) * A ^ (2 : ℝ) := by
    intro x
    have hb := enorm_integralKernel_le k f (fun x => (hkx x).enorm)
      hf.aemeasurable.enorm x
    calc ‖integralKernel (ν := ν) k f x‖ₑ ^ (2 : ℝ)
        ≤ ((∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) * A) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hb (by norm_num)
      _ = (∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ) ∂ν) * A ^ (2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
          norm_num
  have hint : ∫⁻ x, ‖integralKernel (ν := ν) k f x‖ₑ ^ (2 : ℝ) ∂μ
      ≤ (∫⁻ z, ‖k z‖ₑ ^ (2 : ℝ) ∂(μ.prod ν)) * A ^ (2 : ℝ) := by
    calc ∫⁻ x, ‖integralKernel (ν := ν) k f x‖ₑ ^ (2 : ℝ) ∂μ
        ≤ ∫⁻ x, (∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ) ∂ν) * A ^ (2 : ℝ) ∂μ :=
          lintegral_mono hptw
      _ = (∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ) ∂ν ∂μ) * A ^ (2 : ℝ) := by
          rw [lintegral_mul_const'' _ ((hk.aemeasurable.enorm.pow_const
            (2 : ℝ)).lintegral_prod_right')]
      _ = (∫⁻ z, ‖k z‖ₑ ^ (2 : ℝ) ∂(μ.prod ν)) * A ^ (2 : ℝ) := by
          rw [← lintegral_prod _ (hk.aemeasurable.enorm.pow_const (2 : ℝ))]
  -- Take square roots.
  calc eLpNorm (integralKernel (ν := ν) k f) 2 μ
      = (∫⁻ x, ‖integralKernel (ν := ν) k f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        eLpNorm_two_eq_rpow μ _ hKf
    _ ≤ ((∫⁻ z, ‖k z‖ₑ ^ (2 : ℝ) ∂(μ.prod ν)) * A ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow hint (by norm_num)
    _ = (∫⁻ z, ‖k z‖ₑ ^ (2 : ℝ) ∂(μ.prod ν)) ^ (1 / (2 : ℝ)) * A := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num
    _ = eLpNorm k 2 (μ.prod ν) * eLpNorm f 2 ν := by
        rw [eLpNorm_two_eq_rpow (μ.prod ν) _ hk, hA, eLpNorm_two_eq_rpow ν _ hf]

end HilbertSchmidt

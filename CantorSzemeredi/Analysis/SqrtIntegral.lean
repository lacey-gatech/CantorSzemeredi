/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import Mathlib

/-!
# Cauchy–Schwarz and Minkowski for `√(∫ f²)`

Mathlib states the `L²` inequalities for `eLpNorm`, which is `ℝ≥0∞`-valued.  The conditional
norms of a Hilbert module are real numbers depending on a base point, and they are integrated
again over a fibre, so carrying them as `eLpNorm` means moving in and out of `ℝ≥0∞` at every
step.  This file states the two inequalities directly for `Real.sqrt (∫ f ^ 2)`.
-/

namespace SqrtIntegral

open MeasureTheory

variable {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ}

/-- Cauchy–Schwarz: `|∫ f g| ≤ √(∫ f²) √(∫ g²)`. -/
theorem abs_integral_mul_le {f g : γ → ℝ} (hf : MemLp f 2 ρ) (hg : MemLp g 2 ρ) :
    |∫ z, f z * g z ∂ρ| ≤ Real.sqrt (∫ z, f z ^ 2 ∂ρ) * Real.sqrt (∫ z, g z ^ 2 ∂ρ) := by
  have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
  have hfa : MemLp (fun z => |f z|) (ENNReal.ofReal (2 : ℝ)) ρ := by rw [← h2]; exact hf.abs
  have hga : MemLp (fun z => |g z|) (ENNReal.ofReal (2 : ℝ)) ρ := by rw [← h2]; exact hg.abs
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ρ) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun z => abs_nonneg (f z))
    (Filter.Eventually.of_forall fun z => abs_nonneg (g z)) hfa hga
  have hsq : ∀ c : ℝ, |c| ^ (2 : ℝ) = c ^ 2 := fun c => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  calc |∫ z, f z * g z ∂ρ| ≤ ∫ z, |f z * g z| ∂ρ := abs_integral_le_integral_abs
    _ = ∫ z, |f z| * |g z| ∂ρ := by simp [abs_mul]
    _ ≤ (∫ z, |f z| ^ (2 : ℝ) ∂ρ) ^ (1 / (2 : ℝ))
          * (∫ z, |g z| ^ (2 : ℝ) ∂ρ) ^ (1 / (2 : ℝ)) := hholder
    _ = Real.sqrt (∫ z, f z ^ 2 ∂ρ) * Real.sqrt (∫ z, g z ^ 2 ∂ρ) := by
        simp_rw [hsq]
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- `∫ f²` is non-negative. -/
theorem integral_sq_nonneg (f : γ → ℝ) : 0 ≤ ∫ z, f z ^ 2 ∂ρ :=
  integral_nonneg fun z => sq_nonneg _

/-- Minkowski: `√(∫ (f+g)²) ≤ √(∫ f²) + √(∫ g²)`. -/
theorem sqrt_integral_add_sq_le {f g : γ → ℝ} (hf : MemLp f 2 ρ) (hg : MemLp g 2 ρ) :
    Real.sqrt (∫ z, (f z + g z) ^ 2 ∂ρ)
      ≤ Real.sqrt (∫ z, f z ^ 2 ∂ρ) + Real.sqrt (∫ z, g z ^ 2 ∂ρ) := by
  have hff : Integrable (fun z => f z ^ 2) ρ := by simp_rw [sq]; exact hf.integrable_mul hf
  have hgg : Integrable (fun z => g z ^ 2) ρ := by simp_rw [sq]; exact hg.integrable_mul hg
  have hfg : Integrable (fun z => f z * g z) ρ := hf.integrable_mul hg
  have hexp : ∫ z, (f z + g z) ^ 2 ∂ρ
      = (∫ z, f z ^ 2 ∂ρ) + 2 * (∫ z, f z * g z ∂ρ) + (∫ z, g z ^ 2 ∂ρ) := by
    have hrw : (fun z => (f z + g z) ^ 2)
        = ((fun z => f z ^ 2) + fun z => 2 * (f z * g z)) + fun z => g z ^ 2 := by
      funext z
      simp only [Pi.add_apply]
      ring
    rw [hrw, integral_add' (hff.add (hfg.const_mul 2)) hgg, integral_add' hff (hfg.const_mul 2),
      integral_const_mul]
  set A := ∫ z, f z ^ 2 ∂ρ
  set B := ∫ z, g z ^ 2 ∂ρ
  have hA : 0 ≤ A := integral_sq_nonneg f
  have hB : 0 ≤ B := integral_sq_nonneg g
  have hcs : ∫ z, f z * g z ∂ρ ≤ Real.sqrt A * Real.sqrt B :=
    le_trans (le_abs_self _) (abs_integral_mul_le hf hg)
  have hbound : ∫ z, (f z + g z) ^ 2 ∂ρ ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := by
    rw [hexp, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
    linarith
  calc Real.sqrt (∫ z, (f z + g z) ^ 2 ∂ρ) ≤ Real.sqrt ((Real.sqrt A + Real.sqrt B) ^ 2) :=
        Real.sqrt_le_sqrt hbound
    _ = Real.sqrt A + Real.sqrt B :=
        Real.sqrt_sq (by positivity)

/-- `√(∫ ·²)` is monotone under a pointwise bound. -/
theorem sqrt_integral_sq_mono {u v : γ → ℝ} (h : ∀ᵐ z ∂ρ, |u z| ≤ v z)
    (hu : Integrable (fun z => u z ^ 2) ρ) (hv : Integrable (fun z => v z ^ 2) ρ) :
    Real.sqrt (∫ z, u z ^ 2 ∂ρ) ≤ Real.sqrt (∫ z, v z ^ 2 ∂ρ) := by
  refine Real.sqrt_le_sqrt (integral_mono_ae hu hv ?_)
  filter_upwards [h] with z hz
  calc u z ^ 2 = |u z| ^ 2 := (sq_abs _).symm
    _ ≤ v z ^ 2 := by
        have h0 : 0 ≤ |u z| := abs_nonneg _
        nlinarith

/-- `√(∫ (c f)²) = |c| √(∫ f²)`. -/
theorem sqrt_integral_const_mul_sq (c : ℝ) (f : γ → ℝ) :
    Real.sqrt (∫ z, (c * f z) ^ 2 ∂ρ) = |c| * Real.sqrt (∫ z, f z ^ 2 ∂ρ) := by
  have hrw : ∀ z, (c * f z) ^ 2 = c ^ 2 * f z ^ 2 := fun z => by ring
  simp_rw [hrw]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

end SqrtIntegral

/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Cantor.ExpSum

/-!
# The uniform spectral lemma

This file proves Lemma `lem:uniform-spectral` of the blueprint
(`blueprint/src/chapter/cantor.tex`, section "A uniform exponential sum estimate"): if `σ` is a
finite Borel measure on `𝕋 = ℝ / ℤ` without atoms (`NullSingletonClass`) and `s ≥ 1`, then

  `∫ Φ_L (s α) dσ(α) → 0`  as  `L → ∞`.

Everything analytic was done in `CantorSzemeredi.Cantor.ExpSum`; what is left is measure
theory:

* `Φ_L` is `1`-periodic (the `k_n` are integers), so it descends to `𝕋` as `PhiCircle`;
* `Φ_L` is a countable supremum of continuous functions, hence measurable, and `0 ≤ Φ_L ≤ 1`;
* the exceptional set is countable, hence `σ`-null because `σ` has no atoms;
* dominated convergence.

The circle is `AddCircle (1 : ℝ)`, and the dilation `α ↦ s α` of the blueprint is the `ℕ`-scalar
multiple `s • α` on it.
-/

namespace CantorSzemeredi

open Complex Finset MeasureTheory Filter

namespace CantorData

variable (C : CantorData)

/-! ### `Φ` is bounded, periodic and measurable -/

/-- Every window average is an average of unit vectors, so `Φ_L β ≤ 1`. -/
theorem Phi_le_one (L : ℕ) (β : ℝ) : C.Phi L β ≤ 1 := by
  refine Real.iSup_le (fun M => ?_) zero_le_one
  rcases Nat.eq_zero_or_pos L with hL | hL
  · simp [hL]
  · have hL' : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hL', mul_one]
    have hsum := C.norm_sum_Ico_le_card β M (M + L)
    simpa using hsum

/-- Replacing `β` by `β + 1` does not change the exponential sums, since the `k_n` are
integers. -/
theorem sum_Ico_add_one (β : ℝ) (M N : ℕ) :
    ∑ n ∈ Finset.Ico M N, e ((β + 1) * C.enum n)
      = ∑ n ∈ Finset.Ico M N, e (β * C.enum n) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  have hrw : (β + 1) * (C.enum n : ℝ) = β * (C.enum n : ℝ) + (((C.enum n : ℤ)) : ℝ) := by
    push_cast; ring
  rw [hrw, e_add, e_intCast, mul_one]

/-- **`Φ_L` is `1`-periodic**, so it is a function on the circle. -/
theorem Phi_periodic (L : ℕ) : Function.Periodic (C.Phi L) 1 := by
  intro β
  simp only [Phi, C.sum_Ico_add_one]

/-- `Φ_L` is a countable supremum of continuous functions, hence Borel measurable. -/
theorem measurable_Phi (L : ℕ) : Measurable (C.Phi L) := by
  refine Measurable.iSup fun M => Continuous.measurable ?_
  refine continuous_norm.comp (continuous_const.mul ?_)
  exact continuous_finsetSum _ fun n _ => continuous_e.comp (by fun_prop)

/-! ### `Φ` as a function on the circle `𝕋 = ℝ / ℤ` -/

/-- `Φ_L` viewed as a function on `𝕋`. -/
noncomputable def PhiCircle (L : ℕ) : AddCircle (1 : ℝ) → ℝ := (C.Phi_periodic L).lift

@[simp] theorem PhiCircle_coe (L : ℕ) (β : ℝ) :
    C.PhiCircle L (β : AddCircle (1 : ℝ)) = C.Phi L β :=
  Function.Periodic.lift_coe _ _

theorem PhiCircle_nonneg (L : ℕ) (α : AddCircle (1 : ℝ)) : 0 ≤ C.PhiCircle L α := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective α
  rw [show ((QuotientAddGroup.mk x : AddCircle (1 : ℝ))) = ((x : ℝ) : AddCircle (1 : ℝ)) from rfl,
    C.PhiCircle_coe]
  exact C.Phi_nonneg L x

theorem PhiCircle_le_one (L : ℕ) (α : AddCircle (1 : ℝ)) : C.PhiCircle L α ≤ 1 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective α
  rw [show ((QuotientAddGroup.mk x : AddCircle (1 : ℝ))) = ((x : ℝ) : AddCircle (1 : ℝ)) from rfl,
    C.PhiCircle_coe]
  exact C.Phi_le_one L x

theorem measurable_PhiCircle (L : ℕ) : Measurable (C.PhiCircle L) := by
  rw [QuotientAddGroup.measurable_from_quotient]
  have hcomp : (C.PhiCircle L ∘ ((↑) : ℝ → AddCircle (1 : ℝ))) = C.Phi L := by
    funext β
    exact C.PhiCircle_coe L β
  rw [hcomp]
  exact C.measurable_Phi L

end CantorData

/-- Scalar multiples commute with the projection `ℝ → 𝕋`. -/
theorem coe_nsmul_addCircle (s : ℕ) (x : ℝ) :
    (s • ((x : ℝ) : AddCircle (1 : ℝ))) = ((((s : ℝ) * x) : ℝ) : AddCircle (1 : ℝ)) := by
  rw [← nsmul_eq_mul, QuotientAddGroup.mk_nsmul]

/-- The dilation `α ↦ s α` of the circle is measurable. -/
theorem measurable_nsmul_addCircle (s : ℕ) :
    Measurable (fun α : AddCircle (1 : ℝ) => s • α) := by
  rw [QuotientAddGroup.measurable_from_quotient]
  have hcomp : ((fun α : AddCircle (1 : ℝ) => s • α) ∘ ((↑) : ℝ → AddCircle (1 : ℝ)))
      = fun x : ℝ => ((((s : ℝ) * x) : ℝ) : AddCircle (1 : ℝ)) := by
    funext x
    exact coe_nsmul_addCircle s x
  rw [hcomp]
  exact QuotientAddGroup.measurable_coe.comp (by fun_prop)

namespace CantorData

variable (C : CantorData)

/-! ### The exceptional set is countable -/

/-- The set of `α` with `s α` in the exceptional set `E₀`. -/
def excSetSmul (s : ℕ) : Set ℝ := {α : ℝ | ((s : ℝ) * α) ∈ C.excSet}

/-- `{α : s α ∈ E₀}` is countable: it consists of the rationals `k / (b^c · gcd D · s)`. -/
theorem excSetSmul_countable {s : ℕ} (hs : 1 ≤ s) : (C.excSetSmul s).Countable := by
  have hgpos : (0 : ℝ) < (C.gcdDigits : ℝ) := by exact_mod_cast C.gcdDigits_pos
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hbpos : (0 : ℝ) < (C.base : ℝ) := by
    have : 0 < C.base := by have := C.three_le_base; omega
    exact_mod_cast this
  refine Set.Countable.mono ?_
    (Set.countable_range (fun p : ℕ × ℤ =>
      ((p.2 : ℝ) / ((C.base : ℝ) ^ p.1 * (C.gcdDigits : ℝ) * (s : ℝ)))))
  rintro α ⟨c, k, hk⟩
  refine ⟨(c, k), ?_⟩
  have hden : ((C.base : ℝ) ^ c * (C.gcdDigits : ℝ) * (s : ℝ)) ≠ 0 := by positivity
  rw [div_eq_iff hden]
  linear_combination -hk

/-- The image of the exceptional set in the circle. -/
def excCircle (s : ℕ) : Set (AddCircle (1 : ℝ)) :=
  (fun x : ℝ => (x : AddCircle (1 : ℝ))) '' C.excSetSmul s

theorem excCircle_countable {s : ℕ} (hs : 1 ≤ s) : (C.excCircle s).Countable :=
  (C.excSetSmul_countable hs).image _

/-! ### The uniform spectral lemma -/

/-- **Lemma `lem:uniform-spectral`.**  If `σ` is a finite Borel measure on `𝕋` without atoms
and `s ≥ 1`, then `∫ Φ_L (s α) dσ(α) → 0`.

Each `Φ_L` is a countable supremum of continuous functions, hence Borel, with
`0 ≤ Φ_L ≤ 1`; by `tendsto_Phi_zero`, `Φ_L (s α) → 0` off a countable set, which is
`σ`-null since `σ` has no atoms.  Dominated convergence finishes the proof. -/
theorem tendsto_integral_Phi_zero {s : ℕ} (hs : 1 ≤ s) (σ : Measure (AddCircle (1 : ℝ)))
    [IsFiniteMeasure σ] [NullSingletonClass σ] :
    Tendsto (fun L : ℕ => ∫ α, C.PhiCircle L (s • α) ∂σ) atTop (nhds 0) := by
  have hzero : (0 : ℝ) = ∫ _α : AddCircle (1 : ℝ), (0 : ℝ) ∂σ := by simp
  rw [hzero]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_
  · filter_upwards with L
    exact ((C.measurable_PhiCircle L).comp (measurable_nsmul_addCircle s)).aestronglyMeasurable
  · filter_upwards with L
    filter_upwards with α
    rw [Real.norm_eq_abs, abs_of_nonneg (C.PhiCircle_nonneg L _)]
    exact C.PhiCircle_le_one L _
  · exact integrable_const 1
  · have hnull : σ (C.excCircle s) = 0 := (C.excCircle_countable hs).measure_zero σ
    refine Filter.Eventually.mono (compl_mem_ae_iff.2 hnull) ?_
    rintro α hα
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective α
    have hx : ((s : ℝ) * x) ∉ C.excSet := by
      intro hmem
      exact hα ⟨x, hmem, rfl⟩
    have hval : ∀ L : ℕ,
        C.PhiCircle L (s • (QuotientAddGroup.mk x : AddCircle (1 : ℝ)))
          = C.Phi L ((s : ℝ) * x) := by
      intro L
      rw [show (s • (QuotientAddGroup.mk x : AddCircle (1 : ℝ)))
            = ((((s : ℝ) * x) : ℝ) : AddCircle (1 : ℝ)) from coe_nsmul_addCircle s x]
      exact C.PhiCircle_coe L _
    simp only [hval]
    exact C.tendsto_Phi_zero hx

end CantorData

end CantorSzemeredi

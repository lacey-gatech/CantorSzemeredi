/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.Joining
import CantorSzemeredi.Analysis.HilbertSchmidt

/-!
# Reading a kernel on `X × X` fibrewise

Blueprint: the second half of the Hilbert–Schmidt step of `lem:dichotomy`, in
`blueprint/src/chapter/structure.tex`.

The eigenfunction produced by `exists_eigenvector_of_atom` lives in `L²(λ)`, where
`λ = ∫ m_x ⊗ m_x dm(x)` is the relatively independent self-joining.  Since `λ` is an average
of the product measures `m_x ⊗ m_x`, a function square integrable against `λ` is, for almost
every `x`, square integrable against `m_x ⊗ m_x` — that is, it is a Hilbert–Schmidt kernel on
the fibre over `x`.  `CantorSzemeredi/Analysis/HilbertSchmidt.lean` then makes the associated
operator on `L²(m_x)` compact, each `m_x` being a probability measure.

This file is that passage: `lintegral_joining` is the Fubini identity for `λ`,
`ae_memLp_fibre` is the almost-everywhere square integrability on fibres, and
`ae_isCompactOperator_fibre` is the conclusion.

## Measurability

`MemLp H 2 λ` only gives `AEStronglyMeasurable H λ`, which says nothing about any individual
fibre: a `λ`-null set can meet every fibre.  The lemmas below therefore ask for
`StronglyMeasurable H` outright.  That is no loss — `AEStronglyMeasurable.mk` replaces any
`L²(λ)` function by a strongly measurable one agreeing with it `λ`-a.e., and the operator
attached to a kernel depends only on its a.e. class (`integralKernelL_congr`).
-/

namespace CantorSzemeredi

open MeasureTheory ProbabilityTheory HilbertSchmidt

namespace MPS

variable {S : MPS} [StandardBorelSpace S.X]

/-! ### Fubini for a measure composed with a kernel -/

/-- `∫⁻ F d(κ ∘ₘ μ) = ∫⁻ x, (∫⁻ y, F y ∂κ x) ∂μ`.

The Bochner version is `integral_kernel_comp_measure`; this is the `ℝ≥0∞` one, obtained the
same way, by viewing `κ ∘ₘ μ` as a composition of kernels over `Unit`. -/
theorem lintegral_kernel_comp_measure {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (κ : Kernel X Y) [IsSFiniteKernel κ]
    {F : Y → ENNReal} (hF : Measurable F) :
    ∫⁻ y, F y ∂(κ ∘ₘ μ) = ∫⁻ x, (∫⁻ y, F y ∂(κ x)) ∂μ := by
  have hrw : (κ ∘ₘ μ) = (κ ∘ₖ (Kernel.const Unit μ)) () := Measure.comp_eq_comp_const_apply
  rw [hrw, ProbabilityTheory.Kernel.lintegral_comp _ _ _ hF, Kernel.const_apply]

/-- **Fubini for the joining.**  Integration against `λ` is integration against the fibre
product measures, averaged over the base. -/
theorem lintegral_joining (D : Factor S) {F : S.X × S.X → ENNReal} (hF : Measurable F) :
    ∫⁻ p, F p ∂(joining D)
      = ∫⁻ x, (∫⁻ p, F p ∂((condKernel D x).prod (condKernel D x))) ∂S.m := by
  rw [joining, lintegral_kernel_comp_measure _ _ hF]
  refine lintegral_congr fun x => ?_
  rw [Kernel.prod_apply]

/-! ### Square integrability on almost every fibre -/

/-- `L²` membership as finiteness of a single `lintegral`, with a natural number exponent so
that the base and fibre statements are literally the same expression. -/
private theorem memLp_two_iff {γ : Type*} [MeasurableSpace γ] (ρ : Measure γ) {g : γ → ℂ}
    (hg : AEStronglyMeasurable g ρ) :
    MemLp g 2 ρ ↔ (∫⁻ z, ‖g z‖ₑ ^ (2 : ℕ) ∂ρ) ≠ ⊤ := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg]
  norm_num
  constructor
  · intro h hcon
    rw [hcon] at h
    simp [ENNReal.top_rpow_of_pos] at h
  · exact fun h => ENNReal.rpow_lt_top_of_nonneg (by norm_num) h

/-- **The fibrewise reading.**  A strongly measurable kernel in `L²(λ)` is, for almost every
`x`, a kernel in `L²(m_x ⊗ m_x)`. -/
theorem ae_memLp_fibre (D : Factor S) {H : S.X × S.X → ℂ} (hsm : StronglyMeasurable H)
    (hH : MemLp H 2 (joining D)) :
    ∀ᵐ x ∂S.m, MemLp H 2 ((condKernel D x).prod (condKernel D x)) := by
  have hmeas : Measurable fun p : S.X × S.X => ‖H p‖ₑ ^ (2 : ℕ) :=
    hsm.measurable.enorm.pow_const _
  -- The fibre integrals average to the total integral, which is finite.
  have htot : (∫⁻ x, (∫⁻ p, ‖H p‖ₑ ^ (2 : ℕ)
      ∂((condKernel D x).prod (condKernel D x))) ∂S.m) ≠ ⊤ := by
    rw [← lintegral_joining D hmeas]
    exact (memLp_two_iff _ hH.aestronglyMeasurable).mp hH
  -- The inner integral is a measurable function of the base point.
  have hmeasint : Measurable fun x => ∫⁻ p, ‖H p‖ₑ ^ (2 : ℕ)
      ∂((condKernel D x).prod (condKernel D x)) := by
    have hk : ∀ x, (condKernel D ×ₖ condKernel D) x
        = (condKernel D x).prod (condKernel D x) := fun x => Kernel.prod_apply _ _ _
    simp_rw [← hk]
    exact hmeas.lintegral_kernel
  -- So it is finite almost everywhere.
  filter_upwards [(ae_lt_top hmeasint htot).mono fun x hx => hx.ne] with x hx
  exact (memLp_two_iff _ hsm.aestronglyMeasurable).mpr hx

/-! ### Compactness on almost every fibre -/

/-- **The Hilbert–Schmidt step, fibrewise.**  For almost every `x`, the eigenfunction defines a
compact operator on `L²(m_x)`.

`m_x = condKernel D x` is a probability measure, so `isCompactOperator_integralKernelL`
applies on each fibre. -/
theorem ae_isCompactOperator_fibre (D : Factor S) {H : S.X × S.X → ℂ}
    (hsm : StronglyMeasurable H) (hH : MemLp H 2 (joining D)) :
    ∀ᵐ x ∂S.m, ∃ hx : MemLp H 2 ((condKernel D x).prod (condKernel D x)),
      IsCompactOperator (integralKernelL hx) := by
  filter_upwards [ae_memLp_fibre D hsm hH] with x hx
  exact ⟨hx, isCompactOperator_integralKernelL hx⟩

end MPS

end CantorSzemeredi

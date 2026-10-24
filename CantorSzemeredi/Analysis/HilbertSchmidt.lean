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

/-! ### Measurable rectangles form a set semiring

Mathlib has `isSetSemiring_measurableCylinders` for infinite products, but nothing for the
binary product.  This is the input to
`exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring`, which is what makes finite-rank
kernels dense in `L²(μ ⊗ ν)`. -/

/-- The measurable rectangles of `α × β`. -/
def measurableRectangles (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :
    Set (Set (α × β)) :=
  {s | ∃ a b, MeasurableSet a ∧ MeasurableSet b ∧ s = a ×ˢ b}

theorem isSetSemiring_measurableRectangles (α β : Type*) [MeasurableSpace α]
    [MeasurableSpace β] : IsSetSemiring (measurableRectangles α β) := by
  classical
  refine ⟨⟨∅, ∅, MeasurableSet.empty, MeasurableSet.empty, by simp⟩, ?_, ?_⟩
  · rintro _ ⟨a, b, ha, hb, rfl⟩ _ ⟨a', b', ha', hb', rfl⟩
    exact ⟨a ∩ a', b ∩ b', ha.inter ha', hb.inter hb', Set.prod_inter_prod⟩
  · rintro _ ⟨a, b, ha, hb, rfl⟩ _ ⟨a', b', ha', hb', rfl⟩
    refine ⟨{(a ∩ a') ×ˢ (b \ b'), (a \ a') ×ˢ b}, ?_, ?_, ?_⟩
    · intro s hs
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact ⟨a ∩ a', b \ b', ha.inter ha', hb.diff hb', rfl⟩
      · exact ⟨a \ a', b, ha.diff ha', hb, rfl⟩
    · intro s hs t ht hst
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hs ht
      -- The two pieces are separated by membership of the first coordinate in `a'`.
      have hdisj : Disjoint ((a ∩ a') ×ˢ (b \ b')) ((a \ a') ×ˢ b) := by
        rw [Set.disjoint_left]
        rintro ⟨x, y⟩ hx hy
        exact hy.1.2 hx.1.2
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
      · exact absurd rfl hst
      · exact hdisj
      · exact hdisj.symm
      · exact absurd rfl hst
    · ext ⟨x, y⟩
      simp only [Set.mem_sdiff, Set.mem_prod, Finset.coe_insert, Finset.coe_singleton,
        Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union]
      constructor
      · rintro ⟨⟨hxa, hyb⟩, hnot⟩
        by_cases hxa' : x ∈ a'
        · exact Or.inl ⟨⟨hxa, hxa'⟩, hyb, fun hyb' => hnot ⟨hxa', hyb'⟩⟩
        · exact Or.inr ⟨⟨hxa, hxa'⟩, hyb⟩
      · rintro (⟨⟨hxa, hxa'⟩, hyb, hyb'⟩ | ⟨⟨hxa, hxa'⟩, hyb⟩)
        · exact ⟨⟨hxa, hyb⟩, fun h => hyb' h.2⟩
        · exact ⟨⟨hxa, hyb⟩, fun h => hxa' h.1⟩

/-- The rectangles are exactly the collection `generateFrom_prod` is stated for. -/
theorem measurableRectangles_eq (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :
    measurableRectangles α β
      = Set.image2 (· ×ˢ ·) {s : Set α | MeasurableSet s} {t : Set β | MeasurableSet t} := by
  ext s
  simp only [measurableRectangles, Set.mem_ofPred_eq, Set.mem_image2]
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, b, ha, hb, rfl⟩

/-- The rectangles generate the product σ-algebra. -/
theorem generateFrom_measurableRectangles (α β : Type*) [MeasurableSpace α]
    [MeasurableSpace β] :
    MeasurableSpace.generateFrom (measurableRectangles α β) = Prod.instMeasurableSpace := by
  rw [measurableRectangles_eq]
  exact generateFrom_prod

/-- **Set-level density.**  For a finite product measure, every measurable subset of `α × β`
is approximated in symmetric difference by a finite union of measurable rectangles.

This is the step that makes finite-rank kernels dense in `L²(μ ⊗ ν)`, and hence the step that
makes integral operators compact. -/
theorem exists_rectangleUnion_symmDiff_lt {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] [IsFiniteMeasure (μ.prod ν)]
    {s : Set (α × β)} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t ∈ supClosure (measurableRectangles α β), (μ.prod ν) (symmDiff t s) < ε := by
  refine exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
    (isSetSemiring_measurableRectangles α β) ?_
    (generateFrom_measurableRectangles α β).symm hs hε
  -- The whole space is itself a rectangle, so the covering hypothesis is immediate.
  refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
  · rintro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact ⟨Set.univ, Set.univ, MeasurableSet.univ, MeasurableSet.univ, by simp⟩
  · simp

/-! ### Rank-one operators are compact

Mathlib has no "finite rank implies compact" lemma: it has `IsCompactOperator.add`,
`IsCompactOperator.smul` and `isCompactOperator_of_tendsto`, but no base case.  This supplies
it.  A rank-one map `x ↦ φ x • g` sends the unit ball into `{t • g : ‖t‖ ≤ ‖φ‖}`, the image of
a closed ball of `ℂ` under a continuous map, hence compact. -/

theorem isCompactOperator_rankOne {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (φ : E →L[ℂ] ℂ) (g : F) :
    IsCompactOperator (fun x => φ x • g) := by
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨Metric.closedBall (0 : E) 1, Metric.closedBall_mem_nhds 0 one_pos,
    (fun t : ℂ => t • g) '' (Metric.closedBall (0 : ℂ) ‖φ‖), ?_, ?_⟩
  · exact (isCompact_closedBall (0 : ℂ) ‖φ‖).image (continuous_id.smul continuous_const)
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨φ x, ?_, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc ‖φ x‖ ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
      _ ≤ ‖φ‖ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          simpa [Metric.mem_closedBall, dist_zero_right] using hx
      _ = ‖φ‖ := mul_one _

/-- A finite sum of rank-one operators is compact. -/
theorem isCompactOperator_sum_rankOne {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {ι : Type*} (s : Finset ι)
    (φ : ι → (E →L[ℂ] ℂ)) (g : ι → F) :
    IsCompactOperator (fun x => ∑ i ∈ s, φ i x • g i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    have hz : (fun x : E => ∑ j ∈ (∅ : Finset ι), φ j x • g j) = fun _ : E => (0 : F) := by
      funext x
      simp
    rw [hz]
    exact isCompactOperator_zero
  | insert i s hi ih =>
    have hrw : (fun x => ∑ j ∈ insert i s, φ j x • g j)
        = (fun x => φ i x • g i) + fun x => ∑ j ∈ s, φ j x • g j := by
      funext x
      rw [Finset.sum_insert hi]
      rfl
    rw [hrw]
    exact (isCompactOperator_rankOne (φ i) (g i)).add ih

/-! ### The bundled operator

To speak of compactness at all the operator has to be a `ContinuousLinearMap`, since
`isCompactOperator_of_tendsto` is stated for those.  Packaging it needs three things: that the
slices `k (x, ·)` are in `L²(ν)` for a.e. `x`, that the resulting function of `x` is
measurable, and the bound already proved.
-/

variable [SFinite μ]

omit [SFinite μ] in
/-- For a.e. `x`, the slice `k (x, ·)` is square integrable. -/
theorem memLp_slice {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => k (x, y)) 2 ν := by
  have hmeas : ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => k (x, y)) ν :=
    hk.aestronglyMeasurable.prodMk_left
  have hfin : ∫⁻ x, (∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ) ∂ν) ∂μ ≠ ⊤ := by
    rw [← lintegral_prod _ (hk.aestronglyMeasurable.aemeasurable.enorm.pow_const (2 : ℝ))]
    have := hk.eLpNorm_ne_top
    rw [eLpNorm_two_eq_rpow _ _ hk.aestronglyMeasurable] at this
    intro hcon
    exact this (by rw [hcon]; simp)
  have hae : ∀ᵐ x ∂μ, (∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ) ∂ν) ≠ ⊤ :=
    ae_lt_top' (hk.aestronglyMeasurable.aemeasurable.enorm.pow_const (2 : ℝ)).lintegral_prod_right'
      hfin |>.mono fun x hx => hx.ne
  filter_upwards [hmeas, hae] with x hx hx'
  rw [memLp_iff, eLpNorm_two_eq_rpow _ _ hx]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hx'

omit [SFinite μ] in
/-- For a.e. `x`, the integrand of the operator is integrable. -/
theorem integrable_slice_mul {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν))
    {f : β → ℂ} (hf : MemLp f 2 ν) :
    ∀ᵐ x ∂μ, Integrable (fun y => k (x, y) * f y) ν := by
  filter_upwards [memLp_slice hk] with x hx
  exact (MemLp.integrable_mul hx hf)

end HilbertSchmidt

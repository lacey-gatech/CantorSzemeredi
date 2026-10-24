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
theorem enorm_integralKernel_le_of_slice (k : α × β → ℂ) (f : β → ℂ)
    {x : α} (hk : AEMeasurable (fun y => ‖k (x, y)‖ₑ) ν)
    (hf : AEMeasurable (fun y => ‖f y‖ₑ) ν) :
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
        ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hk hf

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
    (hkx : ∀ᵐ x ∂μ, AEMeasurable (fun y => k (x, y)) ν)
    (hf : AEStronglyMeasurable f ν)
    (hKf : AEStronglyMeasurable (integralKernel (ν := ν) k f) μ) :
    eLpNorm (integralKernel (ν := ν) k f) 2 μ
      ≤ eLpNorm k 2 (μ.prod ν) * eLpNorm f 2 ν := by
  -- Write all three `eLpNorm`s as `rpow`s of lintegrals.
  have htwo : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have htop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  set A : ℝ≥0∞ := (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) with hA
  -- Pointwise Cauchy–Schwarz, then integrate in `x`.
  have hptw : ∀ᵐ x ∂μ, ‖integralKernel (ν := ν) k f x‖ₑ ^ (2 : ℝ)
      ≤ (∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ) ∂ν) * A ^ (2 : ℝ) := by
    filter_upwards [hkx] with x hxm
    have hb := enorm_integralKernel_le_of_slice (x := x) k f hxm.enorm
      hf.aemeasurable.enorm
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
          lintegral_mono_ae hptw
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

/-- For a.e. `x`, the integrand of the operator is integrable. -/
theorem integrable_slice_mul {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν))
    {f : β → ℂ} (hf : MemLp f 2 ν) :
    ∀ᵐ x ∂μ, Integrable (fun y => k (x, y) * f y) ν := by
  filter_upwards [memLp_slice hk] with x hx
  exact (MemLp.integrable_mul hx hf)

/-- The image of a square integrable function under the operator is measurable. -/
theorem aestronglyMeasurable_integralKernel {k : α × β → ℂ}
    (hk : AEStronglyMeasurable k (μ.prod ν)) {f : β → ℂ} (hf : AEStronglyMeasurable f ν) :
    AEStronglyMeasurable (integralKernel (ν := ν) k f) μ :=
  (hk.mul hf.comp_snd).integral_prod_right'

/-- The operator maps `L²(ν)` into `L²(μ)`. -/
theorem memLp_integralKernel {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν))
    {f : β → ℂ} (hf : MemLp f 2 ν) :
    MemLp (integralKernel (ν := ν) k f) 2 μ := by
  rw [memLp_iff]
  refine lt_of_le_of_lt (eLpNorm_integralKernel_le hk.aestronglyMeasurable
    (hk.aestronglyMeasurable.prodMk_left.mono fun x hx => hx.aemeasurable)
    hf.aestronglyMeasurable
    (aestronglyMeasurable_integralKernel hk.aestronglyMeasurable hf.aestronglyMeasurable))
    (ENNReal.mul_lt_top hk hf)

/-- The operator as a linear map on `L²`. -/
noncomputable def integralKernelL0 {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_integralKernel hk (Lp.memLp f)).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_integralKernel hk (Lp.memLp (f + g))).coeFn_toLp,
      Lp.coeFn_add ((memLp_integralKernel hk (Lp.memLp f)).toLp _)
        ((memLp_integralKernel hk (Lp.memLp g)).toLp _),
      (memLp_integralKernel hk (Lp.memLp f)).coeFn_toLp,
      (memLp_integralKernel hk (Lp.memLp g)).coeFn_toLp,
      integrable_slice_mul hk (Lp.memLp f), integrable_slice_mul hk (Lp.memLp g)]
      with x hx hxa hx2 hx3 hif hig
    rw [hx, hxa, Pi.add_apply, hx2, hx3, integralKernel, integralKernel, integralKernel,
      ← integral_add hif hig]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy]
    simp [mul_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_integralKernel hk (Lp.memLp (c • f))).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_integralKernel hk (Lp.memLp f)).toLp _),
      (memLp_integralKernel hk (Lp.memLp f)).coeFn_toLp] with x hx hxs hx2
    simp only [RingHom.id_apply]
    rw [hx, hxs, Pi.smul_apply, hx2, integralKernel, integralKernel, ← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy]
    simp [smul_eq_mul]
    ring

/-- **The integral operator as a continuous linear map**, with operator norm at most the
`L²` norm of the kernel.  This is the form `isCompactOperator_of_tendsto` consumes. -/
noncomputable def integralKernelL {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous (integralKernelL0 hk) ((eLpNorm k 2 (μ.prod ν)).toReal) (by
    intro f
    have hbound := eLpNorm_integralKernel_le (μ := μ) (ν := ν) (k := k) (f := ⇑f)
      hk.aestronglyMeasurable
      (hk.aestronglyMeasurable.prodMk_left.mono fun x hx => hx.aemeasurable)
      (Lp.aestronglyMeasurable f)
      (aestronglyMeasurable_integralKernel hk.aestronglyMeasurable (Lp.aestronglyMeasurable f))
    have hnorm : ‖integralKernelL0 hk f‖ = (eLpNorm (integralKernel (ν := ν) k ⇑f) 2 μ).toReal := by
      rw [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_ae (memLp_integralKernel hk (Lp.memLp f)).coeFn_toLp
    rw [hnorm, Lp.norm_def]
    rw [← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (by
      exact ENNReal.mul_ne_top hk.eLpNorm_ne_top (Lp.memLp f).eLpNorm_ne_top) hbound)

@[simp] theorem integralKernelL_apply {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) :
    integralKernelL hk f = (memLp_integralKernel hk (Lp.memLp f)).toLp _ := rfl

/-- The operator norm bound, in the form used for the limiting argument. -/
theorem norm_integralKernelL_le {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    ‖integralKernelL hk‖ ≤ (eLpNorm k 2 (μ.prod ν)).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _


/-! ### Product kernels give rank-one operators -/

/-- A tensor product of two `L²` functions is an `L²` kernel. -/
theorem memLp_prod_mul {g : α → ℂ} {h : β → ℂ} (hg : MemLp g 2 μ) (hh : MemLp h 2 ν) :
    MemLp (fun p : α × β => g p.1 * h p.2) 2 (μ.prod ν) := by
  have hmeas : AEStronglyMeasurable (fun p : α × β => g p.1 * h p.2) (μ.prod ν) :=
    hg.aestronglyMeasurable.comp_fst.mul hh.aestronglyMeasurable.comp_snd
  rw [memLp_iff, eLpNorm_two_eq_rpow _ _ hmeas]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have hsplit : ∀ p : α × β, ‖g p.1 * h p.2‖ₑ ^ (2 : ℝ)
      = ‖g p.1‖ₑ ^ (2 : ℝ) * ‖h p.2‖ₑ ^ (2 : ℝ) := by
    intro p
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  simp_rw [hsplit]
  rw [lintegral_prod_mul
    ((hg.aestronglyMeasurable.enorm.pow_const _))
    ((hh.aestronglyMeasurable.enorm.pow_const _))]
  have hgf : (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ≠ ⊤ := by
    have := memLp_iff.mp hg
    rw [eLpNorm_two_eq_rpow _ _ hg.aestronglyMeasurable] at this
    intro hcon
    rw [hcon] at this
    simp [ENNReal.top_rpow_of_pos] at this
  have hhf : (∫⁻ y, ‖h y‖ₑ ^ (2 : ℝ) ∂ν) ≠ ⊤ := by
    have := memLp_iff.mp hh
    rw [eLpNorm_two_eq_rpow _ _ hh.aestronglyMeasurable] at this
    intro hcon
    rw [hcon] at this
    simp [ENNReal.top_rpow_of_pos] at this
  exact (ENNReal.mul_lt_top hgf.lt_top hhf.lt_top).ne


/-- The operator attached to a tensor product kernel is rank one: it sends `f` to the
scalar `∫ h f` times `g`. -/
theorem integralKernelL_prod_mul {g : α → ℂ} {h : β → ℂ} (hg : MemLp g 2 μ) (hh : MemLp h 2 ν)
    (f : Lp ℂ 2 ν) :
    integralKernelL (memLp_prod_mul hg hh) f = (∫ y, h y * f y ∂ν) • hg.toLp g := by
  refine Lp.ext ?_
  filter_upwards [(memLp_integralKernel (memLp_prod_mul hg hh) (Lp.memLp f)).coeFn_toLp,
    Lp.coeFn_smul (∫ y, h y * f y ∂ν) (hg.toLp g), hg.coeFn_toLp] with x hx hxs hxg
  rw [integralKernelL_apply, hx, hxs, Pi.smul_apply, hxg, integralKernel, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [integral_const_mul, mul_comm]

/-- Hence it is a compact operator. -/
theorem isCompactOperator_integralKernelL_prod_mul {g : α → ℂ} {h : β → ℂ}
    (hg : MemLp g 2 μ) (hh : MemLp h 2 ν) :
    IsCompactOperator (integralKernelL (memLp_prod_mul hg hh)) := by
  have hconj : MemLp (fun y => (starRingEnd ℂ) (h y)) 2 ν := by
    exact hh.star
  have key : ⇑(integralKernelL (memLp_prod_mul hg hh))
      = fun f : Lp ℂ 2 ν => (innerSL ℂ (hconj.toLp _) f) • hg.toLp g := by
    funext f
    rw [integralKernelL_prod_mul hg hh f]
    congr 1
    rw [show ((innerSL ℂ) (MemLp.toLp (fun y => (starRingEnd ℂ) (h y)) hconj)) f
      = inner ℂ (MemLp.toLp (fun y => (starRingEnd ℂ) (h y)) hconj) f from rfl, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hconj.coeFn_toLp] with y hy
    rw [hy]
    simp [RCLike.inner_apply, mul_comm]
  rw [key]
  exact isCompactOperator_rankOne _ _


/-! ### Compactness by approximation in the kernel -/

/-- The assignment `k ↦ T_k` is additive, in the form needed to compare two kernels. -/
theorem integralKernelL_sub {k k' : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν))
    (hk' : MemLp k' 2 (μ.prod ν)) :
    integralKernelL (hk.sub hk') = integralKernelL hk - integralKernelL hk' := by
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [sub_apply]
  refine Lp.ext ?_
  filter_upwards [(memLp_integralKernel (hk.sub hk') (Lp.memLp f)).coeFn_toLp,
    Lp.coeFn_sub ((memLp_integralKernel hk (Lp.memLp f)).toLp _)
      ((memLp_integralKernel hk' (Lp.memLp f)).toLp _),
    (memLp_integralKernel hk (Lp.memLp f)).coeFn_toLp,
    (memLp_integralKernel hk' (Lp.memLp f)).coeFn_toLp,
    integrable_slice_mul hk (Lp.memLp f), integrable_slice_mul hk' (Lp.memLp f)]
    with x hx hxs hx1 hx2 hi1 hi2
  rw [integralKernelL_apply, integralKernelL_apply, integralKernelL_apply, hx, hxs,
    Pi.sub_apply, hx1, hx2, integralKernel, integralKernel, integralKernel,
    ← integral_sub hi1 hi2]
  simp [Pi.sub_apply, sub_mul]

/-- **Compactness is inherited from approximating kernels.**  If `k` is approximated in
`L²(μ⊗ν)` by kernels whose operators are compact, then `T_k` is compact. -/
theorem isCompactOperator_integralKernelL_of_approx {k : α × β → ℂ}
    (hk : MemLp k 2 (μ.prod ν))
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε → ∃ k' : α × β → ℂ, ∃ hk' : MemLp k' 2 (μ.prod ν),
      IsCompactOperator (integralKernelL hk') ∧ eLpNorm (k - k') 2 (μ.prod ν) < ε) :
    IsCompactOperator (integralKernelL hk) := by
  choose kn hkn hcpt hlt using fun n : ℕ =>
    happrox ((n + 1 : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.mpr (by simp))
  refine isCompactOperator_of_tendsto (l := Filter.atTop)
    (F := fun n => integralKernelL (hkn n)) ?_ (.of_forall hcpt)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbd : ∀ n : ℕ, ‖integralKernelL (hkn n) - integralKernelL hk‖ ≤ 1 / (n + 1 : ℝ) := by
    intro n
    have hsub : integralKernelL (hkn n) - integralKernelL hk
        = -(integralKernelL ((hk.sub (hkn n)))) := by
      rw [integralKernelL_sub hk (hkn n)]; abel
    rw [hsub, norm_neg]
    refine (norm_integralKernelL_le (hk.sub (hkn n))).trans ?_
    have := (hlt n).le
    have h1 : ((n + 1 : ℝ≥0∞)⁻¹) ≠ ⊤ := by simp
    calc (eLpNorm (k - kn n) 2 (μ.prod ν)).toReal
        ≤ ((n + 1 : ℝ≥0∞)⁻¹).toReal := ENNReal.toReal_mono h1 this
      _ = 1 / (n + 1 : ℝ) := by
          rw [ENNReal.toReal_inv, one_div]
          congr 1
  refine squeeze_zero (fun n => norm_nonneg _) hbd ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat


/-! ### The kernel map as a bounded operator-valued map -/

/-- The operator depends only on the a.e. class of the kernel. -/
theorem integralKernelL_congr {k k' : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν))
    (hk' : MemLp k' 2 (μ.prod ν)) (h : k =ᵐ[μ.prod ν] k') :
    integralKernelL hk = integralKernelL hk' := by
  refine ContinuousLinearMap.ext fun f => ?_
  refine Lp.ext ?_
  filter_upwards [(memLp_integralKernel hk (Lp.memLp f)).coeFn_toLp,
    (memLp_integralKernel hk' (Lp.memLp f)).coeFn_toLp,
    Measure.ae_ae_of_ae_prod h] with x hx hx' hslice
  rw [integralKernelL_apply, integralKernelL_apply, hx, hx', integralKernel, integralKernel]
  refine integral_congr_ae ?_
  filter_upwards [hslice] with y hy
  rw [hy]

/-- `k ↦ T_k` is additive. -/
theorem integralKernelL_add {k k' : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν))
    (hk' : MemLp k' 2 (μ.prod ν)) :
    integralKernelL (hk.add hk') = integralKernelL hk + integralKernelL hk' := by
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [add_apply]
  refine Lp.ext ?_
  filter_upwards [(memLp_integralKernel (hk.add hk') (Lp.memLp f)).coeFn_toLp,
    Lp.coeFn_add ((memLp_integralKernel hk (Lp.memLp f)).toLp _)
      ((memLp_integralKernel hk' (Lp.memLp f)).toLp _),
    (memLp_integralKernel hk (Lp.memLp f)).coeFn_toLp,
    (memLp_integralKernel hk' (Lp.memLp f)).coeFn_toLp,
    integrable_slice_mul hk (Lp.memLp f), integrable_slice_mul hk' (Lp.memLp f)]
    with x hx hxs hx1 hx2 hi1 hi2
  rw [integralKernelL_apply, integralKernelL_apply, integralKernelL_apply, hx, hxs,
    Pi.add_apply, hx1, hx2, integralKernel, integralKernel, integralKernel,
    ← integral_add hi1 hi2]
  simp [Pi.add_apply, add_mul]

/-- `k ↦ T_k` is homogeneous. -/
theorem integralKernelL_smul (c : ℂ) {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    integralKernelL (hk.const_mul c) = c • integralKernelL hk := by
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [smul_apply]
  refine Lp.ext ?_
  filter_upwards [(memLp_integralKernel (hk.const_mul c) (Lp.memLp f)).coeFn_toLp,
    Lp.coeFn_smul c ((memLp_integralKernel hk (Lp.memLp f)).toLp _),
    (memLp_integralKernel hk (Lp.memLp f)).coeFn_toLp] with x hx hxs hx1
  rw [integralKernelL_apply, integralKernelL_apply, hx, hxs, Pi.smul_apply, hx1,
    integralKernel, integralKernel, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun y => ?_)
  ring


/-- **The kernel map.**  Sending an `L²` kernel to its integral operator is itself a
norm-one bounded linear map. -/
noncomputable def integralKernelCLM :
    Lp ℂ 2 (μ.prod ν) →L[ℂ] (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) :=
  LinearMap.mkContinuous
    { toFun := fun u => integralKernelL (Lp.memLp u)
      map_add' := fun u v => by
        rw [integralKernelL_congr (Lp.memLp (u + v)) ((Lp.memLp u).add (Lp.memLp v))
          (Lp.coeFn_add u v), integralKernelL_add]
      map_smul' := fun c u => by
        have hae : ⇑(c • u) =ᵐ[μ.prod ν] fun p => c * u p := by
          filter_upwards [Lp.coeFn_smul c u] with p hp
          simpa [smul_eq_mul] using hp
        rw [integralKernelL_congr (Lp.memLp (c • u)) ((Lp.memLp u).const_mul c) hae,
          integralKernelL_smul]
        rfl }
    1 (by
      intro u
      refine (norm_integralKernelL_le (Lp.memLp u)).trans ?_
      rw [Lp.norm_def, one_mul])

@[simp] theorem integralKernelCLM_apply (u : Lp ℂ 2 (μ.prod ν)) :
    integralKernelCLM u = integralKernelL (Lp.memLp u) := rfl


/-! ### Kernels orthogonal to every rectangle vanish -/

omit [SFinite ν] in
theorem isPiSystem_measurableRectangles (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :
    IsPiSystem (measurableRectangles α β) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩ _ ⟨a', b', ha', hb', rfl⟩ _
  exact ⟨a ∩ a', b ∩ b', ha.inter ha', hb.inter hb', Set.prod_inter_prod⟩

omit [SFinite ν] in
/-- A function whose integral over every measurable rectangle vanishes is a.e. zero.
The rectangles form a π-system generating the product σ-algebra, so this is Dynkin's lemma. -/
theorem ae_eq_zero_of_forall_setIntegral_rectangle_eq_zero
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {u : α × β → ℂ} (hu : Integrable u (μ.prod ν))
    (h : ∀ a b, MeasurableSet a → MeasurableSet b →
      ∫ p in a ×ˢ b, u p ∂(μ.prod ν) = 0) :
    u =ᵐ[μ.prod ν] 0 := by
  have huniv : ∫ p in (Set.univ : Set (α × β)), u p ∂(μ.prod ν) = 0 := by
    have := h Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    simpa using this
  have key : ∀ t (_ : MeasurableSet t), ∫ p in t, u p ∂(μ.prod ν) = 0 := by
    refine MeasurableSpace.induction_on_inter
      (C := fun t _ => ∫ p in t, u p ∂(μ.prod ν) = 0)
      (generateFrom_measurableRectangles α β).symm (isPiSystem_measurableRectangles α β)
      (by simp) ?_ ?_ ?_
    · rintro _ ⟨a, b, ha, hb, rfl⟩
      exact h a b ha hb
    · intro t htm ht
      have := integral_add_compl htm hu
      rw [ht, zero_add] at this
      rw [this, ← Measure.restrict_univ (μ := μ.prod ν)] at *
      simpa using huniv
    · intro f hdisj hfm hf
      rw [integral_iUnion hfm hdisj hu.integrableOn]
      simp [hf]
  exact hu.ae_eq_zero_of_forall_setIntegral_eq_zero fun t htm _ => key t htm


/-! ### Tensor products span a dense subspace, and compactness follows -/

/-- The tensor product kernels, as a subset of `L²(μ ⊗ ν)`. -/
def prodKernels (μ : Measure α) (ν : Measure β) [SFinite ν] : Set (Lp ℂ 2 (μ.prod ν)) :=
  {v | ∃ (g : α → ℂ) (h : β → ℂ) (hg : MemLp g 2 μ) (hh : MemLp h 2 ν),
    v = (memLp_prod_mul hg hh).toLp _}

/-- **Tensor products are total in `L²(μ ⊗ ν)`.**  Nothing but `0` is orthogonal to all of
them: testing against indicators of rectangles and applying Dynkin's lemma. -/
theorem topologicalClosure_span_prodKernels [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (Submodule.span ℂ (prodKernels μ ν)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  have hrect : ∀ a b, MeasurableSet a → MeasurableSet b →
      ∫ p in a ×ˢ b, (u : α × β → ℂ) p ∂(μ.prod ν) = 0 := by
    intro a b ha hb
    have hg : MemLp (Set.indicator a (fun _ => (1 : ℂ))) 2 μ :=
      memLp_indicator_const 2 ha.nullMeasurableSet 1 (Or.inr (measure_ne_top μ a))
    have hh : MemLp (Set.indicator b (fun _ => (1 : ℂ))) 2 ν :=
      memLp_indicator_const 2 hb.nullMeasurableSet 1 (Or.inr (measure_ne_top ν b))
    have hmem : (memLp_prod_mul hg hh).toLp _ ∈ prodKernels μ ν := ⟨_, _, hg, hh, rfl⟩
    have hinner : inner ℂ ((memLp_prod_mul hg hh).toLp _) u = 0 :=
      hu _ (Submodule.subset_span hmem)
    rw [L2.inner_def] at hinner
    rw [← hinner, ← integral_indicator (ha.prod hb)]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_prod_mul hg hh).coeFn_toLp] with p hp
    rw [hp]
    by_cases hpa : p.1 ∈ a <;> by_cases hpb : p.2 ∈ b <;>
      simp [hpa, hpb, Set.mem_prod, RCLike.inner_apply]
  have hae : (u : α × β → ℂ) =ᵐ[μ.prod ν] 0 :=
    ae_eq_zero_of_forall_setIntegral_rectangle_eq_zero
      ((Lp.memLp u).integrable (by norm_num)) hrect
  exact Submodule.mem_bot ℂ |>.mpr (Lp.eq_zero_iff_ae_eq_zero.mpr hae)


/-- **Integral operators with an `L²` kernel are compact.**

On a finite measure space, every `k ∈ L²(μ ⊗ ν)` gives a compact operator
`L²(ν) → L²(μ)`.  Tensor products give rank-one operators and span a dense subspace,
the Hilbert–Schmidt bound makes `k ↦ T_k` continuous, and compactness is closed under
operator-norm limits. -/
theorem isCompactOperator_integralKernelL [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    IsCompactOperator (integralKernelL hk) := by
  have hK : (Submodule.span ℂ (prodKernels μ ν)).topologicalClosure ≤
      (compactOperator (RingHom.id ℂ) (Lp ℂ 2 ν) (Lp ℂ 2 μ)).comap
        (integralKernelCLM (μ := μ) (ν := ν)).toLinearMap := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · rw [Submodule.span_le]
      rintro v ⟨g, h, hg, hh, rfl⟩
      change IsCompactOperator (integralKernelCLM _)
      rw [integralKernelCLM_apply,
        integralKernelL_congr _ (memLp_prod_mul hg hh) (memLp_prod_mul hg hh).coeFn_toLp]
      exact isCompactOperator_integralKernelL_prod_mul hg hh
    · exact isClosed_setOfPred_isCompactOperator.preimage
        (integralKernelCLM (μ := μ) (ν := ν)).continuous
  have hmem : hk.toLp k ∈ (Submodule.span ℂ (prodKernels μ ν)).topologicalClosure := by
    rw [topologicalClosure_span_prodKernels]
    trivial
  have := hK hmem
  rw [Submodule.mem_comap] at this
  have heq : integralKernelCLM (hk.toLp k) = integralKernelL hk := by
    rw [integralKernelCLM_apply]
    exact integralKernelL_congr _ hk hk.coeFn_toLp
  rwa [show (integralKernelCLM.toLinearMap (hk.toLp k)) = integralKernelL hk from heq] at this

end HilbertSchmidt

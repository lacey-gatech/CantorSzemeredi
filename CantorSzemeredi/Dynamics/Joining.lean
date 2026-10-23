/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.HilbertModule

/-!
# The relatively independent self-joining

Blueprint: `def:joining` and `lem:joining` in `blueprint/src/chapter/mps.tex`.

Over a factor `D`, the measure `m` disintegrates as `m = ∫ m_x dm(x)`, and the *relatively
independent self-joining* is `λ = ∫ m_x ⊗ m_x dm(x)` on `X × X`.  Its two properties:

* `integral_joining` : `∫ a ⊗ a' dλ = ∫ E(a|D) E(a'|D) dm`;
* `joining_invariant` : `λ` is invariant under `R = T × T`.

## Disintegration

Mathlib supplies the disintegration over a sub-σ-algebra as `ProbabilityTheory.condExpKernel`,
with `condExp_ae_eq_integral_condExpKernel` identifying `E(f|D)` with integration against it.
It requires the space to be standard Borel, which is exactly the blueprint's standing
assumption that `X` is a compact metric space with its Borel σ-algebra.
-/

namespace CantorSzemeredi

open MeasureTheory ProbabilityTheory

namespace MPS

/-- A system's space is non-empty: it carries a probability measure. -/
instance nonempty_X (S : MPS) : Nonempty S.X := nonempty_of_isProbabilityMeasure S.m

variable {S : MPS} [StandardBorelSpace S.X]

/-- The disintegration of `m` over the factor `D`: `m = ∫ (condKernel D x) dm(x)`.

`condExpKernel` is a kernel whose *source* carries the sub-σ-algebra `D.σ`; we pull it back
along the identity, which is `𝒜`-`D.σ` measurable because `D.σ ≤ 𝒜`, to get a kernel of the
ambient space to itself. -/
noncomputable def condKernel (D : Factor S) : Kernel S.X S.X :=
  Kernel.comap (condExpKernel S.m D.σ) id (measurable_id'' D.le)

instance (D : Factor S) : IsMarkovKernel (condKernel D) := by
  rw [condKernel]
  infer_instance

/-- **Definition `def:joining`.**  The relatively independent self-joining
`λ = ∫ m_x ⊗ m_x dm(x)` on `X × X`. -/
noncomputable def joining (D : Factor S) : Measure (S.X × S.X) :=
  (condKernel D ×ₖ condKernel D) ∘ₘ S.m

instance (D : Factor S) : IsProbabilityMeasure (joining D) := by
  rw [joining]
  infer_instance

/-- Integration against `condKernel D` computes the conditional expectation. -/
theorem condExp_eq_integral_condKernel (D : Factor S) {a : S.X → ℝ} (ha : Integrable a S.m) :
    S.m[a|D.σ] =ᵐ[S.m] fun x => ∫ y, a y ∂(condKernel D x) := by
  have h := condExp_ae_eq_integral_condExpKernel (μ := S.m) (m := D.σ) D.le ha
  filter_upwards [h] with x hx
  rw [hx, condKernel]
  rfl

/-- `condKernel D x B` is a version of `E(1_B | D)`. -/
theorem condKernel_real_ae_eq (D : Factor S) {B : Set S.X} (hB : MeasurableSet B) :
    (fun x => (condKernel D x).real B) =ᵐ[S.m] S.m⟦B|D.σ⟧ :=
  condExpKernel_ae_eq_condExp (μ := S.m) (m := D.σ) D.le hB

/-- **Equation `eq:joining` on rectangles.**  `λ (B × B') = ∫⁻ κ_x B · κ_x B' dm`. -/
theorem joining_prod_apply (D : Factor S) {B B' : Set S.X}
    (hB : MeasurableSet B) (hB' : MeasurableSet B') :
    joining D (B ×ˢ B') = ∫⁻ x, condKernel D x B * condKernel D x B' ∂S.m := by
  rw [joining, Measure.bind_apply (hB.prod hB') (Kernel.aemeasurable _)]
  refine lintegral_congr fun x => ?_
  rw [Kernel.prod_apply]
  exact Measure.prod_prod _ _

/-! ### The integral against the joining

Mathlib has `lintegral_bind` but no Bochner `integral_bind`.  It does have
`ProbabilityTheory.integral_comp` for a composition of *kernels*, and
`Measure.comp_eq_comp_const_apply` rewrites `κ ∘ₘ μ` as a kernel composition applied at the
unique point of `Unit`.  Routing through that gives the Bochner formula. -/

/-- `∫ F d(κ ∘ₘ μ) = ∫ x, (∫ y, F y ∂κ x) ∂μ`. -/
theorem integral_kernel_comp_measure {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [SFinite μ] (κ : Kernel X Y) [IsSFiniteKernel κ]
    {F : Y → E} (hF : Integrable F (κ ∘ₘ μ)) :
    ∫ y, F y ∂(κ ∘ₘ μ) = ∫ x, (∫ y, F y ∂(κ x)) ∂μ := by
  have hrw : (κ ∘ₘ μ) = (κ ∘ₖ (Kernel.const Unit μ)) () := Measure.comp_eq_comp_const_apply
  rw [hrw] at hF ⊢
  rw [ProbabilityTheory.Kernel.integral_comp hF, Kernel.const_apply]

/-- **Equation `eq:joining`.**  `∫ a ⊗ a' dλ = ∫ E(a|D) E(a'|D) dm`, for bounded measurable
`a` and `a'`. -/
theorem integral_joining (D : Factor S) {a a' : S.X → ℝ} {C C' : ℝ}
    (hma : Measurable a) (hma' : Measurable a')
    (hba : ∀ x, |a x| ≤ C) (hba' : ∀ x, |a' x| ≤ C') :
    ∫ p : S.X × S.X, a p.1 * a' p.2 ∂(joining D)
      = ∫ x, (S.m[a|D.σ]) x * (S.m[a'|D.σ]) x ∂S.m := by
  classical
  -- Bounded measurable functions are integrable against every probability measure here.
  have hint : ∀ (ν : Measure S.X) [IsProbabilityMeasure ν], Integrable a ν := by
    intro ν _
    refine MemLp.integrable (q := ⊤) le_top ?_
    exact memLp_top_of_bound hma.aestronglyMeasurable C (Filter.Eventually.of_forall fun x =>
      by simpa [Real.norm_eq_abs] using hba x)
  have hint' : ∀ (ν : Measure S.X) [IsProbabilityMeasure ν], Integrable a' ν := by
    intro ν _
    refine MemLp.integrable (q := ⊤) le_top ?_
    exact memLp_top_of_bound hma'.aestronglyMeasurable C' (Filter.Eventually.of_forall fun x =>
      by simpa [Real.norm_eq_abs] using hba' x)
  have hprodint : Integrable (fun p : S.X × S.X => a p.1 * a' p.2) (joining D) := by
    refine MemLp.integrable (q := ⊤) le_top ?_
    refine memLp_top_of_bound
      ((hma.comp measurable_fst).mul (hma'.comp measurable_snd)).aestronglyMeasurable (C * C') ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul]
    have h₁ : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hba p.1)
    exact mul_le_mul (hba p.1) (hba' p.2) (abs_nonneg _) h₁
  -- Expand the joining as a composition and use the product structure fibrewise.
  rw [joining, integral_kernel_comp_measure _ _ (by rwa [← joining])]
  refine integral_congr_ae ?_
  filter_upwards [condExp_eq_integral_condKernel D (hint S.m),
    condExp_eq_integral_condKernel D (hint' S.m)] with x hx hx'
  rw [hx, hx']
  have hfib : (condKernel D ×ₖ condKernel D) x
      = (condKernel D x).prod (condKernel D x) := Kernel.prod_apply _ _ _
  rw [hfib, integral_prod_mul]

/-! ### Equivariance of the disintegration

The content of `lem:joining`'s invariance claim: the conditional measures satisfy
`m_x (T⁻¹ B) = m_{Tx} (B)` almost everywhere.  This is `condExp_comp` read through the
identification of the kernel with conditional expectation. -/

theorem condKernel_real_comp (D : Factor S) {B : Set S.X} (hB : MeasurableSet B) :
    (fun x => (condKernel D x).real (S.T ⁻¹' B))
      =ᵐ[S.m] fun x => (condKernel D (S.T x)).real B := by
  classical
  set f : S.X → ℝ := B.indicator (fun _ => (1 : ℝ)) with hf
  have hfint : Integrable f S.m := by
    rw [hf]
    exact (integrable_const (1 : ℝ)).indicator hB
  have hpre : (S.T ⁻¹' B).indicator (fun _ => (1 : ℝ)) = f ∘ S.T := by
    funext x
    by_cases hx : S.T x ∈ B <;> simp [hf, Set.indicator, hx]
  -- The left side is `E(1_{T⁻¹B} | D)`.
  have h₁ : (fun x => (condKernel D x).real (S.T ⁻¹' B))
      =ᵐ[S.m] S.m[(S.T ⁻¹' B).indicator (fun _ => (1 : ℝ))|D.σ] :=
    condKernel_real_ae_eq D (hB.preimage S.measurable_T)
  -- Which equals `E(1_B | D) ∘ T` by `condExp_comp`.
  have h₂ : S.m[(S.T ⁻¹' B).indicator (fun _ => (1 : ℝ))|D.σ] =ᵐ[S.m] (S.m[f|D.σ]) ∘ S.T := by
    rw [hpre]
    exact (Factor.condExp_comp D hfint).symm
  -- And the right side is also `E(1_B|D) ∘ T`, by composing the kernel identity with `T`.
  have h₃ : (fun x => (condKernel D (S.T x)).real B) =ᵐ[S.m] (S.m[f|D.σ]) ∘ S.T :=
    S.measurePreserving.quasiMeasurePreserving.ae_eq_comp (condKernel_real_ae_eq D hB)
  exact (h₁.trans h₂).trans h₃.symm

/-- The `ℝ≥0∞`-valued form of equivariance. -/
theorem condKernel_comp (D : Factor S) {B : Set S.X} (hB : MeasurableSet B) :
    (fun x => condKernel D x (S.T ⁻¹' B)) =ᵐ[S.m] fun x => condKernel D (S.T x) B := by
  filter_upwards [condKernel_real_comp D hB] with x hx
  have h₁ : condKernel D x (S.T ⁻¹' B) ≠ ⊤ := measure_ne_top _ _
  have h₂ : condKernel D (S.T x) B ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal h₁, ← ENNReal.ofReal_toReal h₂]
  exact congrArg ENNReal.ofReal hx

/-! ### Invariance of the joining -/

/-- The product transformation `R = T × T` on `X × X`. -/
def prodMap (S : MPS) : S.X × S.X → S.X × S.X := fun p => (S.T p.1, S.T p.2)

theorem measurable_prodMap (S : MPS) : Measurable (prodMap S) :=
  (S.measurable_T.comp measurable_fst).prodMk (S.measurable_T.comp measurable_snd)

/-- `λ` and `λ ∘ R⁻¹` agree on measurable rectangles. -/
theorem joining_comap_prod_apply (D : Factor S) {B B' : Set S.X}
    (hB : MeasurableSet B) (hB' : MeasurableSet B') :
    joining D (prodMap S ⁻¹' (B ×ˢ B')) = joining D (B ×ˢ B') := by
  have hpre : prodMap S ⁻¹' (B ×ˢ B') = (S.T ⁻¹' B) ×ˢ (S.T ⁻¹' B') := rfl
  rw [hpre, joining_prod_apply D (hB.preimage S.measurable_T) (hB'.preimage S.measurable_T),
    joining_prod_apply D hB hB']
  -- Replace each kernel value by its value at `T x`, then change variables.
  have hcongr : ∫⁻ x, condKernel D x (S.T ⁻¹' B) * condKernel D x (S.T ⁻¹' B') ∂S.m
      = ∫⁻ x, condKernel D (S.T x) B * condKernel D (S.T x) B' ∂S.m := by
    refine lintegral_congr_ae ?_
    filter_upwards [condKernel_comp D hB, condKernel_comp D hB'] with x hx hx'
    rw [hx, hx']
  rw [hcongr]
  exact S.measurePreserving.lintegral_comp
    (((condKernel D).measurable_coe hB).mul ((condKernel D).measurable_coe hB'))

/-- **Lemma `lem:joining`, invariance.**  `λ` is invariant under `R = T × T`.

Measurable rectangles form a π-system generating the product σ-algebra, and the two
probability measures agree on them. -/
theorem joining_invariant (D : Factor S) :
    Measure.map (prodMap S) (joining D) = joining D := by
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨B, hB, B', hB', rfl⟩
    rw [Measure.map_apply (measurable_prodMap S) (hB.prod hB')]
    exact joining_comap_prod_apply D hB hB'
  · rw [Measure.map_apply (measurable_prodMap S) MeasurableSet.univ]
    simp

end MPS

end CantorSzemeredi

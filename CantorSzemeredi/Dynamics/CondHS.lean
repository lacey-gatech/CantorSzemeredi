/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.Fibre
import CantorSzemeredi.Dynamics.Extensions
import CantorSzemeredi.Analysis.SqrtIntegral

/-!
# The conditional Hilbert–Schmidt operator

Blueprint: the passage from fibrewise compact operators to conditionally compact functions, in
the Hilbert–Schmidt step of `lem:dichotomy`.

`Fibre.lean` reads an `L²(λ)` kernel `H` fibrewise and gets a compact operator on each
`L²(m_x)`.  Those fibre operators assemble into a single operator on the Hilbert module,

  `(Φ_H a)(x) = ∫ H(x, y) a(y) dm_x(y)` ,

and the point of this file is the estimate that controls it: the conditional norm of `Φ_H a`
is bounded by the conditional Hilbert–Schmidt norm of `H` times a bound for the conditional
norm of `a`.  That is what turns an approximation of the *kernels* into an approximation of
the *functions*, which is what `CondCompact` asks for.

## Two norms

Everything is measured along fibres, against the conditional measures `m_x = condKernel D x`:

* `fibreNorm D g x = (∫ g² dm_x)^{1/2}` — this is `condNorm D g x` (`condNorm_ae_eq_fibreNorm`),
  rewritten so that it can be integrated over a fibre;
* `hsRow D H x = (∫ H(x,y)² dm_x(y))^{1/2}` — the `L²` norm of a single row of the kernel;
* `hsFibre D H x = (∫ (hsRow D H z)² dm_x(z))^{1/2}` — the Hilbert–Schmidt norm of `H` on the
  fibre through `x`, i.e. the `L²(m_x ⊗ m_x)` norm.

## Hypotheses

The estimates below carry their integrability hypotheses explicitly rather than deriving them
from a packaged regularity class.  Conditional expectation gives `a.e.` statements, and an
`a.e.` statement about the base says nothing about any individual fibre until it is pushed
through `ae_ae_condKernel`; keeping the hypotheses visible is what keeps that step honest.
-/

namespace CantorSzemeredi

open MeasureTheory ProbabilityTheory SqrtIntegral

namespace MPS

variable {S : MPS} [StandardBorelSpace S.X]

/-! ### Almost everywhere, fibrewise -/

/-- **The disintegration.**  `m = ∫ m_x dm(x)`.

Mathlib proves this against the trimmed measure (`condExpKernel_comp_trim`); since the kernel
is `D.σ`-measurable, `lintegral_trim` replaces the trim by `m` itself. -/
theorem condKernel_comp_measure (D : Factor S) : (condKernel D) ∘ₘ S.m = S.m := by
  have htrim := condExpKernel_comp_trim (μ := S.m) (m := D.σ) D.le
  ext s hs
  have h1 : ((condKernel D) ∘ₘ S.m) s = ∫⁻ x, condExpKernel S.m D.σ x s ∂S.m := by
    rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
    simp [condKernel, Kernel.comap_apply]
  have h2 : S.m s = ∫⁻ x, condExpKernel S.m D.σ x s ∂(S.m.trim D.le) := by
    conv_lhs => rw [← htrim]
    rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  rw [h1, h2, lintegral_trim D.le (Kernel.measurable_coe (condExpKernel S.m D.σ) hs)]

/-- An almost everywhere statement about the base holds almost everywhere on almost every
fibre.  Immediate from the disintegration: the conditional measures of a null set integrate
to its measure, hence vanish a.e. -/
theorem ae_ae_condKernel (D : Factor S) {p : S.X → Prop}
    (hmeas : MeasurableSet {x | p x}) (h : ∀ᵐ x ∂S.m, p x) :
    ∀ᵐ x ∂S.m, ∀ᵐ y ∂(condKernel D x), p y := by
  have hc : MeasurableSet {x | p x}ᶜ := hmeas.compl
  have h0 : ∫⁻ x, condKernel D x {x | p x}ᶜ ∂S.m = 0 := by
    rw [← Measure.bind_apply hc (Kernel.aemeasurable _), condKernel_comp_measure]
    rw [ae_iff] at h
    simpa [Set.compl_ofPred] using h
  rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hc)] at h0
  filter_upwards [h0] with x hx
  rw [ae_iff]
  simpa [Set.compl_ofPred] using hx

/-! ### Fibre norms -/

/-- The `L²` norm of `g` over the fibre through `x`. -/
noncomputable def fibreNorm (D : Factor S) (g : S.X → ℝ) : S.X → ℝ :=
  fun x => Real.sqrt (∫ y, g y ^ 2 ∂(condKernel D x))

/-- The `L²` norm of the row `H(x, ·)` over the fibre through `x`. -/
noncomputable def hsRow (D : Factor S) (H : S.X × S.X → ℝ) : S.X → ℝ :=
  fun x => Real.sqrt (∫ y, H (x, y) ^ 2 ∂(condKernel D x))

/-- The Hilbert–Schmidt norm of `H` on the fibre through `x`: the `L²(m_x ⊗ m_x)` norm. -/
noncomputable def hsFibre (D : Factor S) (H : S.X × S.X → ℝ) : S.X → ℝ :=
  fun x => Real.sqrt (∫ z, hsRow D H z ^ 2 ∂(condKernel D x))

theorem fibreNorm_nonneg (D : Factor S) (g : S.X → ℝ) (x : S.X) : 0 ≤ fibreNorm D g x :=
  Real.sqrt_nonneg _

theorem hsRow_nonneg (D : Factor S) (H : S.X × S.X → ℝ) (x : S.X) : 0 ≤ hsRow D H x :=
  Real.sqrt_nonneg _

theorem hsFibre_nonneg (D : Factor S) (H : S.X × S.X → ℝ) (x : S.X) : 0 ≤ hsFibre D H x :=
  Real.sqrt_nonneg _

/-- The conditional norm *is* the fibre `L²` norm. -/
theorem condNorm_ae_eq_fibreNorm (D : Factor S) {g : S.X → ℝ} (hg : Integrable (g * g) S.m) :
    condNorm D g =ᵐ[S.m] fibreNorm D g := by
  filter_upwards [condExp_eq_integral_condKernel D hg] with x hx
  rw [condNorm, condInner, hx, fibreNorm]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [Pi.mul_apply, sq]


/-! ### The operator -/

/-- **The conditional Hilbert–Schmidt operator**
`(Φ_H a)(x) = ∫ H(x, y) a(y) dm_x(y)`. -/
noncomputable def condIntegralOp (D : Factor S) (H : S.X × S.X → ℝ) (a : S.X → ℝ) : S.X → ℝ :=
  fun x => ∫ y, H (x, y) * a y ∂(condKernel D x)

/-- The operator is additive in the kernel. -/
theorem condIntegralOp_sub (D : Factor S) (H K : S.X × S.X → ℝ) (a : S.X → ℝ) {x : S.X}
    (hH : Integrable (fun y => H (x, y) * a y) (condKernel D x))
    (hK : Integrable (fun y => K (x, y) * a y) (condKernel D x)) :
    condIntegralOp D (H - K) a x = condIntegralOp D H a x - condIntegralOp D K a x := by
  rw [condIntegralOp, condIntegralOp, condIntegralOp, ← integral_sub hH hK]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [Pi.sub_apply, sub_mul]

/-- **Fibrewise Cauchy–Schwarz.**  `|Φ_H a (x)| ≤ ‖H(x,·)‖_{L²(m_x)} ‖a‖_{L²(m_x)}`. -/
theorem abs_condIntegralOp_le (D : Factor S) {H : S.X × S.X → ℝ} {a : S.X → ℝ} {x : S.X}
    (hH : MemLp (fun y => H (x, y)) 2 (condKernel D x))
    (ha : MemLp a 2 (condKernel D x)) :
    |condIntegralOp D H a x| ≤ hsRow D H x * fibreNorm D a x := by
  have hint : Integrable (fun y => H (x, y) * a y) (condKernel D x) := hH.integrable_mul ha
  have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
  have hHa : MemLp (fun y => |H (x, y)|) (ENNReal.ofReal (2 : ℝ)) (condKernel D x) := by
    rw [← h2]; exact hH.abs
  have haa : MemLp (fun y => |a y|) (ENNReal.ofReal (2 : ℝ)) (condKernel D x) := by
    rw [← h2]; exact ha.abs
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := condKernel D x)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun y => abs_nonneg (H (x, y)))
    (Filter.Eventually.of_forall fun y => abs_nonneg (a y)) hHa haa
  have hsq : ∀ (c : ℝ), |c| ^ (2 : ℝ) = c ^ 2 := by
    intro c
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  calc |condIntegralOp D H a x| ≤ ∫ y, |H (x, y) * a y| ∂(condKernel D x) :=
        abs_integral_le_integral_abs
    _ = ∫ y, |H (x, y)| * |a y| ∂(condKernel D x) := by simp [abs_mul]
    _ ≤ (∫ y, |H (x, y)| ^ (2 : ℝ) ∂(condKernel D x)) ^ (1 / (2 : ℝ))
          * (∫ y, |a y| ^ (2 : ℝ) ∂(condKernel D x)) ^ (1 / (2 : ℝ)) := hholder
    _ = hsRow D H x * fibreNorm D a x := by
        simp_rw [hsq]
        rw [hsRow, fibreNorm, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]


/-! ### The estimate that drives conditional compactness

`‖Φ_H a‖_{E|D} ≤ C ‖H‖_{HS, fibre}` whenever `‖a‖_{E|D} ≤ C`.  Applied to a *difference* of
kernels, this is what converts an approximation of kernels into an approximation of
functions. -/

/-- **The conditional Hilbert–Schmidt bound.**  If the conditional norm of `a` is at most `C`,
then the conditional norm of `Φ_H a` is at most `C` times the fibre Hilbert–Schmidt norm
of `H`. -/
theorem fibreNorm_condIntegralOp_le (D : Factor S) {H : S.X × S.X → ℝ} {a : S.X → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hrow : ∀ᵐ z ∂S.m, MemLp (fun y => H (z, y)) 2 (condKernel D z))
    (hamem : ∀ᵐ z ∂S.m, MemLp a 2 (condKernel D z))
    (hbd : ∀ᵐ z ∂S.m, fibreNorm D a z ≤ C)
    (hmrow : Measurable (hsRow D H)) (hmop : Measurable (condIntegralOp D H a))
    (hintrow : ∀ᵐ x ∂S.m, Integrable (fun z => C ^ 2 * hsRow D H z ^ 2) (condKernel D x))
    (hintop : ∀ᵐ x ∂S.m, Integrable (fun z => condIntegralOp D H a z ^ 2) (condKernel D x)) :
    ∀ᵐ x ∂S.m, fibreNorm D (condIntegralOp D H a) x ≤ C * hsFibre D H x := by
  -- The pointwise bound on the base, from Cauchy–Schwarz on each fibre.
  have hptw : ∀ᵐ z ∂S.m, condIntegralOp D H a z ^ 2 ≤ C ^ 2 * hsRow D H z ^ 2 := by
    filter_upwards [hrow, hamem, hbd] with z hz ha hbz
    have hcs := abs_condIntegralOp_le D hz ha
    have hle : |condIntegralOp D H a z| ≤ hsRow D H z * C :=
      hcs.trans (mul_le_mul_of_nonneg_left hbz (hsRow_nonneg D H z))
    have := mul_self_le_mul_self (abs_nonneg _) hle
    calc condIntegralOp D H a z ^ 2 = |condIntegralOp D H a z| * |condIntegralOp D H a z| := by
          rw [sq, abs_mul_abs_self]
      _ ≤ (hsRow D H z * C) * (hsRow D H z * C) := this
      _ = C ^ 2 * hsRow D H z ^ 2 := by ring
  -- Which transfers to almost every fibre.
  have hPmeas : MeasurableSet {z | condIntegralOp D H a z ^ 2 ≤ C ^ 2 * hsRow D H z ^ 2} :=
    measurableSet_le (hmop.pow_const 2) ((hmrow.pow_const 2).const_mul _)
  filter_upwards [ae_ae_condKernel D hPmeas hptw, hintrow, hintop] with x hx hir hio
  -- Integrate the bound over the fibre and take square roots.
  have hmono : ∫ z, condIntegralOp D H a z ^ 2 ∂(condKernel D x)
      ≤ ∫ z, C ^ 2 * hsRow D H z ^ 2 ∂(condKernel D x) := integral_mono_ae hio hir hx
  have hconst : ∫ z, C ^ 2 * hsRow D H z ^ 2 ∂(condKernel D x)
      = C ^ 2 * ∫ z, hsRow D H z ^ 2 ∂(condKernel D x) := integral_const_mul _ _
  rw [fibreNorm, hsFibre]
  calc Real.sqrt (∫ z, condIntegralOp D H a z ^ 2 ∂(condKernel D x))
      ≤ Real.sqrt (C ^ 2 * ∫ z, hsRow D H z ^ 2 ∂(condKernel D x)) := by
        rw [← hconst]; exact Real.sqrt_le_sqrt hmono
    _ = C * Real.sqrt (∫ z, hsRow D H z ^ 2 ∂(condKernel D x)) := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]


/-! ### From a net of kernels to a net of functions -/

omit [StandardBorelSpace S.X] in
/-- The conditional norm sees only the a.e. class. -/
theorem condNorm_congr_ae (D : Factor S) {g g' : S.X → ℝ} (h : g =ᵐ[S.m] g') :
    condNorm D g =ᵐ[S.m] condNorm D g' := by
  have hmul : (g * g : S.X → ℝ) =ᵐ[S.m] g' * g' := by
    filter_upwards [h] with x hx
    simp [Pi.mul_apply, hx]
  filter_upwards [condExp_congr_ae hmul] with x hx
  rw [condNorm, condNorm, condInner, condInner, hx]

/-- The a.e. form of additivity in the kernel. -/
theorem condIntegralOp_sub_ae (D : Factor S) {H K : S.X × S.X → ℝ} {a : S.X → ℝ}
    (hH : ∀ᵐ z ∂S.m, MemLp (fun y => H (z, y)) 2 (condKernel D z))
    (hK : ∀ᵐ z ∂S.m, MemLp (fun y => K (z, y)) 2 (condKernel D z))
    (ha : ∀ᵐ z ∂S.m, MemLp a 2 (condKernel D z)) :
    ∀ᵐ x ∂S.m,
      condIntegralOp D (H - K) a x = condIntegralOp D H a x - condIntegralOp D K a x := by
  filter_upwards [hH, hK, ha] with x h1 h2 h3
  exact condIntegralOp_sub D H K a (h1.integrable_mul h3) (h2.integrable_mul h3)

/-- The regularity a kernel needs for the conditional Hilbert–Schmidt estimate.

Each field is an integrability or measurability statement that `MemLp H 2 λ` does not by
itself supply, because an `L²(λ)` bound says nothing about any individual fibre. -/
structure IsFibreHS (D : Factor S) (a : S.X → ℝ) (H : S.X × S.X → ℝ) : Prop where
  /-- Almost every row of `H` is square integrable on its fibre. -/
  row : ∀ᵐ z ∂S.m, MemLp (fun y => H (z, y)) 2 (condKernel D z)
  /-- The row norms depend measurably on the base point. -/
  measRow : Measurable (hsRow D H)
  /-- The image is measurable. -/
  measOp : Measurable (condIntegralOp D H a)
  /-- The image is square integrable. -/
  memLpOp : MemLp (condIntegralOp D H a) 2 S.m
  /-- The row norms are square integrable along almost every fibre. -/
  intRow : ∀ᵐ x ∂S.m, Integrable (fun z => hsRow D H z ^ 2) (condKernel D x)
  /-- So is the image. -/
  intOp : ∀ᵐ x ∂S.m, Integrable (fun z => condIntegralOp D H a z ^ 2) (condKernel D x)

/-- **The conditional Hilbert–Schmidt bound, in conditional norms.** -/
theorem condNorm_condIntegralOp_le (D : Factor S) {H : S.X × S.X → ℝ} {a : S.X → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hH : IsFibreHS D a H)
    (hamem : ∀ᵐ z ∂S.m, MemLp a 2 (condKernel D z))
    (hbd : ∀ᵐ z ∂S.m, fibreNorm D a z ≤ C) :
    ∀ᵐ x ∂S.m, condNorm D (condIntegralOp D H a) x ≤ C * hsFibre D H x := by
  filter_upwards [condNorm_ae_eq_fibreNorm D (hH.memLpOp.integrable_mul hH.memLpOp),
    fibreNorm_condIntegralOp_le D hC hH.row hamem hbd hH.measRow hH.measOp
      (hH.intRow.mono fun x hx => hx.const_mul _) hH.intOp] with x h1 h2
  rw [h1]
  exact h2

/-- **Conditional compactness from a net of kernels.**

If the orbit of `f` is realised by a family of kernels `K n` acting on a single module element
`a`, and the `K n` admit finite nets in the fibre Hilbert–Schmidt norm, then `f` is
conditionally compact: the conditional Hilbert–Schmidt bound turns closeness of kernels into
closeness of functions, uniformly over the fibres.

This is the step that converts the fibrewise compactness of `Fibre.lean` into the
`CondCompact` of `def:compact-extension`. -/
theorem condCompact_of_kernel_net (D E : Factor S) {f a : S.X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hamem : ∀ᵐ z ∂S.m, MemLp a 2 (condKernel D z))
    (hbd : ∀ᵐ z ∂S.m, fibreNorm D a z ≤ C)
    {K : ℤ → S.X × S.X → ℝ}
    (hKrow : ∀ n : ℤ, ∀ᵐ z ∂S.m, MemLp (fun y => K n (z, y)) 2 (condKernel D z))
    (horbit : ∀ n : ℤ, f ∘ S.iter n =ᵐ[S.m] condIntegralOp D (K n) a)
    (hnet : ∀ δ : ℝ, 0 < δ → ∃ (r : ℕ) (J : Fin r → S.X × S.X → ℝ),
      (∀ q, MemModule D E (condIntegralOp D (J q) a)) ∧
      (∀ q, ∀ᵐ z ∂S.m, MemLp (fun y => J q (z, y)) 2 (condKernel D z)) ∧
      (∀ n : ℤ, ∃ q : Fin r, IsFibreHS D a (K n - J q) ∧
        ∀ᵐ x ∂S.m, hsFibre D (K n - J q) x < δ)) :
    CondCompact D E f := by
  intro ε hε
  -- Scale the kernel accuracy by the bound on `a`.
  have hCpos : 0 < C + 1 := by linarith
  obtain ⟨r, J, hJmod, hJrow, hJnet⟩ := hnet (ε / (C + 1)) (by positivity)
  refine ⟨r, fun q => condIntegralOp D (J q) a, hJmod, fun n => ?_⟩
  obtain ⟨q, hHS, hsmall⟩ := hJnet n
  refine ⟨q, ?_⟩
  -- Rewrite the difference of functions as the operator of the difference of kernels.
  have hdiff : (f ∘ S.iter n) - condIntegralOp D (J q) a
      =ᵐ[S.m] condIntegralOp D (K n - J q) a := by
    filter_upwards [horbit n, condIntegralOp_sub_ae D (hKrow n) (hJrow q) hamem]
      with x hx hsub
    rw [Pi.sub_apply, hx, hsub]
  filter_upwards [condNorm_congr_ae D hdiff,
    condNorm_condIntegralOp_le D hC hHS hamem hbd, hsmall] with x hcongr hle hlt
  rw [hcongr]
  calc condNorm D (condIntegralOp D (K n - J q) a) x ≤ C * hsFibre D (K n - J q) x := hle
    _ ≤ C * (ε / (C + 1)) := by
        rcases eq_or_lt_of_le hC with h | h
        · simp [← h]
        · exact mul_le_mul_of_nonneg_left hlt.le hC
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hCpos]
        nlinarith



/-! ### Discharging the regularity hypotheses

The measurability obligations in `IsFibreReg` and `IsFibreHS` are not extra assumptions on the
kernel: they follow from joint measurability of `H`, through Mathlib's measurability of a
Bochner integral against a kernel.  And `rowL2`, a condition on almost every fibre, reduces
to a single `L²(m)` condition on the base, by the disintegration. -/

/-- The disintegration, for `ℝ≥0∞`-valued integrals. -/
theorem lintegral_condKernel (D : Factor S) {g : S.X → ENNReal} (hg : Measurable g) :
    ∫⁻ z, g z ∂S.m = ∫⁻ x, (∫⁻ z, g z ∂(condKernel D x)) ∂S.m := by
  conv_lhs => rw [← condKernel_comp_measure D]
  exact lintegral_kernel_comp_measure _ _ hg

/-- A function square integrable on the base is square integrable on almost every fibre. -/
theorem ae_memLp_condKernel (D : Factor S) {g : S.X → ℝ} (hg : StronglyMeasurable g)
    (hmem : MemLp g 2 S.m) :
    ∀ᵐ x ∂S.m, MemLp g 2 (condKernel D x) := by
  have hmeas : Measurable fun z => ‖g z‖ₑ ^ (2 : ℕ) := hg.measurable.enorm.pow_const _
  have htot : (∫⁻ x, (∫⁻ z, ‖g z‖ₑ ^ (2 : ℕ) ∂(condKernel D x)) ∂S.m) ≠ ⊤ := by
    rw [← lintegral_condKernel D hmeas]
    exact (memLp_two_iff_lintegral hmem.aestronglyMeasurable).mp hmem
  have hmi : Measurable fun x => ∫⁻ z, ‖g z‖ₑ ^ (2 : ℕ) ∂(condKernel D x) :=
    hmeas.lintegral_kernel
  filter_upwards [(ae_lt_top hmi htot).mono fun x hx => hx.ne] with x hx
  exact (memLp_two_iff_lintegral hg.aestronglyMeasurable).mpr hx

/-- **The row norms are measurable.**  `x ↦ ‖H(x,·)‖_{L²(m_x)}` is a square root of a Bochner
integral against the kernel, and those are measurable in the base point. -/
theorem measurable_hsRow (D : Factor S) {H : S.X × S.X → ℝ} (hH : StronglyMeasurable H) :
    Measurable (hsRow D H) := by
  have h1 : StronglyMeasurable fun p : S.X × S.X => H p ^ 2 := by
    simp_rw [sq]
    exact hH.mul hH
  have h2 : StronglyMeasurable fun x => ∫ y, H (x, y) ^ 2 ∂(condKernel D x) :=
    h1.integral_kernel_prod_right' (κ := condKernel D)
  exact Real.continuous_sqrt.measurable.comp h2.measurable

/-- **The image of the operator is measurable.** -/
theorem measurable_condIntegralOp (D : Factor S) {H : S.X × S.X → ℝ} {a : S.X → ℝ}
    (hH : StronglyMeasurable H) (ha : StronglyMeasurable a) :
    Measurable (condIntegralOp D H a) := by
  have h1 : StronglyMeasurable fun p : S.X × S.X => H p * a p.2 :=
    hH.mul (ha.comp_measurable measurable_snd)
  exact (h1.integral_kernel_prod_right' (κ := condKernel D)).measurable

/-! ### Scaling and the triangle inequality for the fibre norms -/

/-- Fibre regularity: what a kernel needs for the fibre norms to behave. -/
structure IsFibreReg (D : Factor S) (H : S.X × S.X → ℝ) : Prop where
  /-- Almost every row is square integrable on its fibre. -/
  row : ∀ᵐ z ∂S.m, MemLp (fun y => H (z, y)) 2 (condKernel D z)
  /-- The row norms are measurable in the base point. -/
  measRow : Measurable (hsRow D H)
  /-- The row norms are square integrable along almost every fibre. -/
  rowL2 : ∀ᵐ x ∂S.m, MemLp (hsRow D H) 2 (condKernel D x)

theorem hsRow_const_mul (D : Factor S) (c : ℝ) (H : S.X × S.X → ℝ) (x : S.X) :
    hsRow D (fun p => c * H p) x = |c| * hsRow D H x :=
  sqrt_integral_const_mul_sq c _

theorem hsFibre_const_mul (D : Factor S) (c : ℝ) (H : S.X × S.X → ℝ) (x : S.X) :
    hsFibre D (fun p => c * H p) x = |c| * hsFibre D H x := by
  rw [hsFibre, hsFibre]
  simp_rw [hsRow_const_mul D c H]
  rw [sqrt_integral_const_mul_sq |c| _, abs_abs]

theorem hsRow_add_le (D : Factor S) {H K : S.X × S.X → ℝ} {x : S.X}
    (hH : MemLp (fun y => H (x, y)) 2 (condKernel D x))
    (hK : MemLp (fun y => K (x, y)) 2 (condKernel D x)) :
    hsRow D (fun p => H p + K p) x ≤ hsRow D H x + hsRow D K x :=
  sqrt_integral_add_sq_le hH hK

/-- **The triangle inequality for the fibre Hilbert–Schmidt norm.**  Minkowski twice: once
inside each fibre for the rows, once across the fibre for the row norms. -/
theorem hsFibre_add_le (D : Factor S) {H K : S.X × S.X → ℝ}
    (hH : IsFibreReg D H) (hK : IsFibreReg D K) (hHK : IsFibreReg D (fun p => H p + K p)) :
    ∀ᵐ x ∂S.m, hsFibre D (fun p => H p + K p) x ≤ hsFibre D H x + hsFibre D K x := by
  have hptw : ∀ᵐ z ∂S.m, hsRow D (fun p => H p + K p) z ≤ hsRow D H z + hsRow D K z := by
    filter_upwards [hH.row, hK.row] with z h1 h2
    exact hsRow_add_le D h1 h2
  have hset : MeasurableSet {z | hsRow D (fun p => H p + K p) z ≤ hsRow D H z + hsRow D K z} :=
    measurableSet_le hHK.measRow (hH.measRow.add hK.measRow)
  filter_upwards [ae_ae_condKernel D hset hptw, hH.rowL2, hK.rowL2, hHK.rowL2]
    with x hx h1 h2 h3
  have hint3 : Integrable (fun z => hsRow D (fun p => H p + K p) z ^ 2) (condKernel D x) := by
    simp_rw [sq]
    exact h3.integrable_mul h3
  have hintsum : Integrable (fun z => (hsRow D H z + hsRow D K z) ^ 2) (condKernel D x) := by
    have hsum := h1.add h2
    simp_rw [sq]
    exact hsum.integrable_mul hsum
  calc hsFibre D (fun p => H p + K p) x
      ≤ Real.sqrt (∫ z, (hsRow D H z + hsRow D K z) ^ 2 ∂(condKernel D x)) := by
        refine sqrt_integral_sq_mono ?_ hint3 hintsum
        filter_upwards [hx] with z hz
        rw [abs_of_nonneg (hsRow_nonneg D _ z)]
        exact hz
    _ ≤ hsFibre D H x + hsFibre D K x := sqrt_integral_add_sq_le h1 h2


/-! ### The finite net

No measurable selection is involved.  The eigenfunction's orbit is a *circle*: `H ∘ Rⁿ`
traces `(cos nθ, sin nθ)` through the real span of the real and imaginary parts of `H`.  So
the orbit of kernels is the image of a bounded subset of `ℝ²` under a map that is Lipschitz
for the fibre Hilbert–Schmidt norm, and the finite net comes from total boundedness of that
parameter set — a fact about `ℝ²`, not about the fibres. -/

/-- The real two-parameter family of kernels spanned by `H₀` and `H₁`. -/
def kerComb (H₀ H₁ : S.X × S.X → ℝ) (v : ℝ × ℝ) : S.X × S.X → ℝ :=
  fun p => v.1 * H₀ p + v.2 * H₁ p

omit [StandardBorelSpace S.X] in
theorem kerComb_sub (H₀ H₁ : S.X × S.X → ℝ) (v w : ℝ × ℝ) :
    (fun p => kerComb H₀ H₁ v p - kerComb H₀ H₁ w p) = kerComb H₀ H₁ (v - w) := by
  funext p
  simp only [kerComb, Prod.fst_sub, Prod.snd_sub]
  ring

theorem IsFibreReg.const_mul {D : Factor S} {H : S.X × S.X → ℝ} (h : IsFibreReg D H) (c : ℝ) :
    IsFibreReg D (fun p => c * H p) := by
  have hrow : hsRow D (fun p => c * H p) = fun x => |c| * hsRow D H x :=
    funext (hsRow_const_mul D c H)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [h.row] with z hz
    exact hz.const_mul c
  · rw [hrow]
    exact h.measRow.const_mul _
  · filter_upwards [h.rowL2] with x hx
    rw [hrow]
    exact hx.const_mul _

/-- **Fibre regularity, with the measurability discharged.**  What is left to supply is a
condition on the rows and a single `L²(m)` bound on the row norms. -/
theorem isFibreReg_of_memLp_hsRow (D : Factor S) {H : S.X × S.X → ℝ}
    (hH : StronglyMeasurable H)
    (hrow : ∀ᵐ z ∂S.m, MemLp (fun y => H (z, y)) 2 (condKernel D z))
    (hL2 : MemLp (hsRow D H) 2 S.m) :
    IsFibreReg D H :=
  ⟨hrow, measurable_hsRow D hH,
    ae_memLp_condKernel D (measurable_hsRow D hH).stronglyMeasurable hL2⟩

/-- **`IsFibreHS` with the measurability discharged.**  What is left to supply is a condition
on the rows and two `L²(m)` bounds on the base: everything fibrewise follows. -/
theorem isFibreHS_of_memLp (D : Factor S) {H : S.X × S.X → ℝ} {a : S.X → ℝ}
    (hH : StronglyMeasurable H) (ha : StronglyMeasurable a)
    (hrow : ∀ᵐ z ∂S.m, MemLp (fun y => H (z, y)) 2 (condKernel D z))
    (hL2row : MemLp (hsRow D H) 2 S.m) (hL2op : MemLp (condIntegralOp D H a) 2 S.m) :
    IsFibreHS D a H := by
  refine ⟨hrow, measurable_hsRow D hH, measurable_condIntegralOp D hH ha, hL2op, ?_, ?_⟩
  · filter_upwards [ae_memLp_condKernel D (measurable_hsRow D hH).stronglyMeasurable hL2row]
      with x hx
    simp_rw [sq]
    exact hx.integrable_mul hx
  · filter_upwards [ae_memLp_condKernel D
      (measurable_condIntegralOp D hH ha).stronglyMeasurable hL2op] with x hx
    simp_rw [sq]
    exact hx.integrable_mul hx

/-- The fibre Hilbert–Schmidt norm is Lipschitz in the parameter. -/
theorem hsFibre_kerComb_le (D : Factor S) {H₀ H₁ : S.X × S.X → ℝ} {M : ℝ}
    (hreg0 : IsFibreReg D H₀) (hreg1 : IsFibreReg D H₁)
    (hreg : ∀ v : ℝ × ℝ, IsFibreReg D (kerComb H₀ H₁ v))
    (hb0 : ∀ᵐ x ∂S.m, hsFibre D H₀ x ≤ M) (hb1 : ∀ᵐ x ∂S.m, hsFibre D H₁ x ≤ M)
    (v : ℝ × ℝ) :
    ∀ᵐ x ∂S.m, hsFibre D (kerComb H₀ H₁ v) x ≤ (|v.1| + |v.2|) * M := by
  filter_upwards [hsFibre_add_le D (hreg0.const_mul v.1) (hreg1.const_mul v.2) (hreg v),
    hb0, hb1] with x hx h0 h1
  calc hsFibre D (kerComb H₀ H₁ v) x
      ≤ hsFibre D (fun p => v.1 * H₀ p) x + hsFibre D (fun p => v.2 * H₁ p) x := hx
    _ = |v.1| * hsFibre D H₀ x + |v.2| * hsFibre D H₁ x := by
        rw [hsFibre_const_mul, hsFibre_const_mul]
    _ ≤ |v.1| * M + |v.2| * M := by
        have ha := mul_le_mul_of_nonneg_left h0 (abs_nonneg v.1)
        have hb := mul_le_mul_of_nonneg_left h1 (abs_nonneg v.2)
        linarith
    _ = (|v.1| + |v.2|) * M := by ring

/-- **A finite net of kernels.**  A bounded two-parameter family admits, for every `δ > 0`, a
finite set of parameters approximating it to within `δ` in the fibre Hilbert–Schmidt norm,
uniformly over the fibres. -/
theorem exists_kernel_net (D : Factor S) {H₀ H₁ : S.X × S.X → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hreg0 : IsFibreReg D H₀) (hreg1 : IsFibreReg D H₁)
    (hreg : ∀ v : ℝ × ℝ, IsFibreReg D (kerComb H₀ H₁ v))
    (hb0 : ∀ᵐ x ∂S.m, hsFibre D H₀ x ≤ M) (hb1 : ∀ᵐ x ∂S.m, hsFibre D H₁ x ≤ M)
    (u : ℤ → ℝ × ℝ) (hu : ∀ n, u n ∈ Metric.closedBall (0 : ℝ × ℝ) 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (r : ℕ) (w : Fin r → ℝ × ℝ), ∀ n : ℤ, ∃ q : Fin r, ∀ᵐ x ∂S.m,
      hsFibre D (fun p => kerComb H₀ H₁ (u n) p - kerComb H₀ H₁ (w q) p) x < δ := by
  classical
  set η : ℝ := δ / (2 * M + 2) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  obtain ⟨t, htfin, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (0 : ℝ × ℝ) 1).totallyBounded η hηpos
  set T := htfin.toFinset with hT
  refine ⟨T.card, fun q => (T.equivFin.symm q : ℝ × ℝ), fun n => ?_⟩
  obtain ⟨y, hyt, hy⟩ : ∃ y ∈ t, u n ∈ Metric.ball y η := by
    have := hcover (hu n)
    simpa only [Set.mem_iUnion, exists_prop] using this
  have hyT : y ∈ T := by rwa [hT, Set.Finite.mem_toFinset]
  refine ⟨T.equivFin ⟨y, hyT⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  rw [kerComb_sub]
  -- The parameter difference is small in each coordinate.
  have hdist : dist (u n) y < η := hy
  have hco : |(u n - y).1| + |(u n - y).2| ≤ 2 * η := by
    have h1 : |(u n).1 - y.1| ≤ dist (u n) y := by
      rw [Prod.dist_eq, ← Real.dist_eq]
      exact le_max_left _ _
    have h2 : |(u n).2 - y.2| ≤ dist (u n) y := by
      rw [Prod.dist_eq, ← Real.dist_eq]
      exact le_max_right _ _
    simp only [Prod.fst_sub, Prod.snd_sub]
    linarith
  filter_upwards [hsFibre_kerComb_le D hreg0 hreg1 hreg hb0 hb1 (u n - y)] with x hx
  calc hsFibre D (kerComb H₀ H₁ (u n - y)) x ≤ (|(u n - y).1| + |(u n - y).2|) * M := hx
    _ ≤ (2 * η) * M := by gcongr
    _ < δ := by
        have hpos : (0 : ℝ) < 2 * M + 2 := by linarith
        rw [hηdef, show 2 * (δ / (2 * M + 2)) * M = δ * (2 * M) / (2 * M + 2) by
          field_simp, div_lt_iff₀ hpos]
        nlinarith


/-- **Conditional compactness for a circle orbit.**

If the orbit of `f` is realised by kernels drawn from a bounded two-parameter family acting on
a single module element, then `f` is conditionally compact.  This is the case the dichotomy
needs: the eigenfunction `H` of the Koopman operator on the self-joining has
`H ∘ Rⁿ = e(nθ) H`, so the orbit of kernels is the circle traced by `(cos nθ, sin nθ)`
through the real span of the real and imaginary parts of `H`.

The finite net of module elements comes from total boundedness of the parameter set, and the
conditional Hilbert–Schmidt bound carries it over to the functions. -/
theorem condCompact_of_param_orbit (D E : Factor S) {f a : S.X → ℝ}
    {H₀ H₁ : S.X × S.X → ℝ} {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hamem : ∀ᵐ z ∂S.m, MemLp a 2 (condKernel D z))
    (hbd : ∀ᵐ z ∂S.m, fibreNorm D a z ≤ C)
    (hreg0 : IsFibreReg D H₀) (hreg1 : IsFibreReg D H₁)
    (hreg : ∀ v : ℝ × ℝ, IsFibreReg D (kerComb H₀ H₁ v))
    (hb0 : ∀ᵐ x ∂S.m, hsFibre D H₀ x ≤ M) (hb1 : ∀ᵐ x ∂S.m, hsFibre D H₁ x ≤ M)
    (u : ℤ → ℝ × ℝ) (hu : ∀ n, u n ∈ Metric.closedBall (0 : ℝ × ℝ) 1)
    (horbit : ∀ n : ℤ, f ∘ S.iter n =ᵐ[S.m] condIntegralOp D (kerComb H₀ H₁ (u n)) a)
    (hmod : ∀ v : ℝ × ℝ, MemModule D E (condIntegralOp D (kerComb H₀ H₁ v) a))
    (hHS : ∀ v w : ℝ × ℝ, IsFibreHS D a (kerComb H₀ H₁ v - kerComb H₀ H₁ w)) :
    CondCompact D E f := by
  refine condCompact_of_kernel_net D E hC hamem hbd
    (K := fun n => kerComb H₀ H₁ (u n)) (fun n => (hreg (u n)).row) horbit ?_
  intro δ hδ
  obtain ⟨r, w, hw⟩ := exists_kernel_net D hM hreg0 hreg1 hreg hb0 hb1 u hu hδ
  refine ⟨r, fun q => kerComb H₀ H₁ (w q), fun q => hmod (w q),
    fun q => (hreg (w q)).row, fun n => ?_⟩
  obtain ⟨q, hq⟩ := hw n
  exact ⟨q, hHS (u n) (w q), hq⟩

end MPS

end CantorSzemeredi

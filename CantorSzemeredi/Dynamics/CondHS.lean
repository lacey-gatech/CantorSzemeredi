/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.Fibre
import CantorSzemeredi.Dynamics.Extensions

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

open MeasureTheory ProbabilityTheory

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

end MPS

end CantorSzemeredi

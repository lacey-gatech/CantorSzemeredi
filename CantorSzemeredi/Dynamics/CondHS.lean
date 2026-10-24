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

end MPS

end CantorSzemeredi

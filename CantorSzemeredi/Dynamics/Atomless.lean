/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.Koopman
import CantorSzemeredi.Dynamics.Extensions
import CantorSzemeredi.Dynamics.SpectralExists

/-!
# Conditional weak mixing gives atomless spectral measures

Blueprint: `lem:atomless` in `blueprint/src/chapter/mps.tex`, part (i).

If `f` is conditionally weakly mixing then its spectral measure, for the Koopman operator of
`T`, has no atoms.  The chain is: the Fourier coefficients of `σ_f` are the correlations
`⟪f, Uⁿ f⟫`; those are integrals of `⟨Tⁿ f, f⟩_{E|D}`, so bounded by its `L¹(D)` norm;
conditional weak mixing makes the Cesàro means of those norms vanish; and Wiener's lemma
turns that into the absence of atoms.

## State

The pieces of that chain are proved here:

* `inner_koopman_zpow_eq_integral` — the correlations as integrals over `X`;
* `toLpC`, `inner_toLpC` — a bounded real `f` as an element of the complex `L²`, and its
  correlations as the real integrals `∫ f · (f ∘ Tⁿ)`;
* `integral_eq_integral_condInner` — those integrals are integrals of `⟨Tⁿ f, f⟩_{E|D}`.

What is **not** yet assembled is the final step: converting the `eLpNorm` in the definition of
`CondWeaklyMixing` into the bound `E_N ∫ |⟨Tⁿf,f⟩_{E|D}| → 0` on the Cesàro means, and feeding
it to `noAtoms_of_tendsto_cesaro_zero`.  Part (ii) of the lemma — the statement for
`G = f ⊗ f` on `L²(λ)` with `R = T × T`, and the identity \eqref{eq:psi-identity} — needs the
product system `(X × X, λ, T × T)` as an `MPS`, which is not built yet; `joining_invariant`
supplies its invariance and `integral_joining` the identity.
-/

namespace CantorSzemeredi

open MeasureTheory

namespace MPS

variable {S : MPS}

/-- The Fourier coefficients of the spectral measure are the correlations of the Koopman
orbit, written as integrals over `X`. -/
theorem inner_koopman_zpow_eq_integral (g : Lp ℂ 2 S.m) (n : ℤ) :
    (inner ℂ g ((S.koopman ^ n) g) : ℂ)
      = ∫ x, (starRingEnd ℂ) (g x) * g (S.iter n x) ∂S.m := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [S.coeFn_koopman_zpow n g] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

/-! ### From a bounded real function -/

variable (S)

/-- A bounded measurable real function, as an element of the complex `L²` space. -/
noncomputable def toLpC {f : S.X → ℝ} {C : ℝ} (hm : Measurable f) (hb : ∀ x, |f x| ≤ C) :
    Lp ℂ 2 S.m :=
  MemLp.toLp (fun x => (f x : ℂ))
    (memLp_top_of_bound (Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa using hb x) |>.mono_exponent le_top)

variable {S}

theorem coeFn_toLpC {f : S.X → ℝ} {C : ℝ} (hm : Measurable f) (hb : ∀ x, |f x| ≤ C) :
    toLpC S hm hb =ᵐ[S.m] fun x => ((f x : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

/-- The correlations of a real function are real: integrals of `f · (f ∘ Tⁿ)`. -/
theorem inner_toLpC (D : Factor S) {f : S.X → ℝ} {C : ℝ}
    (hm : Measurable f) (hb : ∀ x, |f x| ≤ C) (n : ℕ) :
    (inner ℂ (toLpC S hm hb) ((S.koopman ^ (n : ℤ)) (toLpC S hm hb)) : ℂ)
      = ((∫ x, f x * f (S.T^[n] x) ∂S.m : ℝ) : ℂ) := by
  rw [inner_koopman_zpow_eq_integral]
  have hpull : (fun x => (starRingEnd ℂ) ((toLpC S hm hb) x)
      * (toLpC S hm hb) (S.iter (n : ℤ) x))
      =ᵐ[S.m] fun x => ((f x * f (S.T^[n] x) : ℝ) : ℂ) := by
    have h₁ := coeFn_toLpC hm hb
    have h₂ := (S.measurePreserving_iter (n : ℤ)).quasiMeasurePreserving.ae_eq_comp h₁
    filter_upwards [h₁, h₂] with x hx hx'
    have hx'' : (toLpC S hm hb) (S.iter (n : ℤ) x) = ((f (S.iter (n : ℤ) x) : ℝ) : ℂ) := hx'
    rw [hx, hx'']
    simp [Complex.conj_ofReal, iter_natCast]
  rw [integral_congr_ae hpull, integral_complex_ofReal]

/-- The correlation is the integral of the conditional inner product. -/
theorem integral_eq_integral_condInner (D : Factor S) {f : S.X → ℝ} {C : ℝ}
    (hm : Measurable f) (hb : ∀ x, |f x| ≤ C) (n : ℕ) :
    ∫ x, f x * f (S.T^[n] x) ∂S.m = ∫ x, condInner D (f ∘ S.T^[n]) f x ∂S.m := by
  have hint : Integrable ((f ∘ S.T^[n]) * f) S.m := by
    refine MemLp.integrable (q := ⊤) le_top ?_
    refine memLp_top_of_bound
      (((hm.comp (S.measurable_T.iterate n)).mul hm).aestronglyMeasurable) (C * C) ?_
    filter_upwards with x
    have h₀ : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hb x)
    simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hb _) (hb _) (abs_nonneg _) h₀
  rw [condInner, integral_condExp D.le]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

end MPS

end CantorSzemeredi

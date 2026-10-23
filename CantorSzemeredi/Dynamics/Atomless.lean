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

Part (i) is proved, as `noAtoms_specMeasure_of_condWeaklyMixing`.

Part (ii) — the statement for `G = f ⊗ f` on `L²(λ)` with `R = T × T`, together with the
identity `eq:psi-identity` — is not formalized.  It needs the product system
`(X × X, λ, T × T)` built as an `MPS`: `joining_invariant` supplies its invariance and
`integral_joining` the identity, so what remains there is construction rather than new
mathematics.
-/

namespace CantorSzemeredi

open MeasureTheory

open scoped ENNReal

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
theorem inner_toLpC {f : S.X → ℝ} {C : ℝ}
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

/-! ### From conditional weak mixing to vanishing Cesàro means -/

/-- The conditional correlations are integrable, and so are their absolute values. -/
theorem integrable_abs_condInner (D : Factor S) {f : S.X → ℝ} {C : ℝ}
    (hm : Measurable f) (hb : ∀ x, |f x| ≤ C) (n : ℕ) :
    Integrable (fun x => |condInner D (f ∘ S.T^[n]) f x|) S.m := by
  have hprod : Integrable ((f ∘ S.T^[n]) * f) S.m := by
    refine MemLp.integrable (q := ⊤) le_top ?_
    refine memLp_top_of_bound
      (((hm.comp (S.measurable_T.iterate n)).mul hm).aestronglyMeasurable) (C * C) ?_
    filter_upwards with x
    have h₀ : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hb x)
    simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hb _) (hb _) (abs_nonneg _) h₀
  exact (integrable_condExp (μ := S.m) (m := D.σ) (f := (f ∘ S.T^[n]) * f)).abs

/-- **The Cesàro means of the `L¹(D)` norms of the correlations vanish.**

This is the step from the `eLpNorm` in the definition of `CondWeaklyMixing` to the bound
Wiener's lemma consumes: on a probability space `L¹ ≤ L²`. -/
theorem tendsto_cesaro_integral_abs_condInner (D : Factor S) {f : S.X → ℝ} {C : ℝ}
    (hm : Measurable f) (hb : ∀ x, |f x| ≤ C) (hcwm : CondWeaklyMixing D f) :
    Filter.Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ∫ x, |condInner D (f ∘ S.T^[n]) f x| ∂S.m)
      Filter.atTop (nhds 0) := by
  set h : ℕ → S.X → ℝ := fun N x =>
    (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, |condInner D (f ∘ S.T^[n]) f x| with hdef
  have hnn : ∀ N x, 0 ≤ h N x := by
    intro N x
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => abs_nonneg _)
  have hintN : ∀ N, Integrable (h N) S.m := fun N =>
    (integrable_finsetSum _ fun n _ => integrable_abs_condInner D hm hb n).const_mul _
  -- `∫ h N` is the average of the integrals.
  have hsplit : ∀ N : ℕ, ∫ x, h N x ∂S.m
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          ∫ x, |condInner D (f ∘ S.T^[n]) f x| ∂S.m := by
    intro N
    rw [hdef]
    rw [integral_const_mul, integral_finsetSum _ fun n _ => integrable_abs_condInner D hm hb n]
  -- `L¹ ≤ L²` on a probability space.
  have hL12 : ∀ N, ENNReal.ofReal (∫ x, h N x ∂S.m) ≤ eLpNorm (h N) 2 S.m := by
    intro N
    have h1 : ENNReal.ofReal (∫ x, h N x ∂S.m) = eLpNorm (h N) 1 S.m := by
      rw [eLpNorm_one_eq_lintegral_enorm (hintN N).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (hintN N)]
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
        (Real.norm_of_nonneg (hnn N x)).symm)
    rw [h1]
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := S.m) (f := h N)
      (p := 1) (q := 2) (by norm_num) (hintN N).aestronglyMeasurable
    simpa using this
  -- Squeeze in `ℝ≥0∞`, then come back to `ℝ`.
  have hsq : Filter.Tendsto (fun N => ENNReal.ofReal (∫ x, h N x ∂S.m))
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcwm
      (Filter.Eventually.of_forall fun N => by simp)
      (Filter.Eventually.of_forall hL12)
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hsq
  simp only [Function.comp_def, ENNReal.toReal_zero] at hreal
  refine hreal.congr fun N => ?_
  rw [ENNReal.toReal_ofReal (by
    rw [hsplit N] at *
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => integral_nonneg fun x =>
      abs_nonneg _)), hsplit N]

/-! ### Lemma `lem:atomless`(i) -/

/-- **Lemma `lem:atomless`(i).**  A conditionally weakly mixing `f` has atomless spectral
measure for the Koopman operator of `T`. -/
theorem noAtoms_specMeasure_of_condWeaklyMixing (D : Factor S) {f : S.X → ℝ} {C : ℝ}
    (hm : Measurable f) (hb : ∀ x, |f x| ≤ C) (hcwm : CondWeaklyMixing D f) :
    ∀ θ : Torus, specMeasure S.koopman (toLpC S hm hb) {θ} = 0 := by
  set F := toLpC S hm hb with hF
  set σ := specMeasure S.koopman F with hσ
  have hspec := hasSpectralMeasure_specMeasure S.koopman F
  set φ : ℕ → ℝ := fun n => ∫ x, |condInner D (f ∘ S.T^[n]) f x| ∂S.m with hφ
  have hφnn : ∀ n, 0 ≤ φ n := fun n => integral_nonneg fun x => abs_nonneg _
  -- Each Fourier coefficient is bounded by `φ n`, and by `‖F‖²`.
  have hbound : ∀ n : ℕ, ‖sigmaHat σ (n : ℤ)‖ ≤ φ n := by
    intro n
    have heq : sigmaHat σ (n : ℤ) = ((∫ x, f x * f (S.T^[n] x) ∂S.m : ℝ) : ℂ) := by
      rw [sigmaHat, ← hspec.inner_eq (n : ℤ), inner_toLpC hm hb n]
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      integral_eq_integral_condInner D hm hb n]
    exact abs_integral_le_integral_abs
  have hbound2 : ∀ n : ℕ, ‖sigmaHat σ (n : ℤ)‖ ≤ ‖F‖ ^ 2 := by
    intro n
    rw [sigmaHat, ← hspec.inner_eq (n : ℤ)]
    calc ‖(inner ℂ F ((S.koopman ^ (n : ℤ)) F) : ℂ)‖
        ≤ ‖F‖ * ‖(S.koopman ^ (n : ℤ)) F‖ := norm_inner_le_norm _ _
      _ = ‖F‖ ^ 2 := by rw [LinearIsometryEquiv.norm_map]; ring
  -- Hence the Cesàro means of `‖σ̂(n)‖²` are dominated by those of `φ`.
  have hdom : ∀ N : ℕ, (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ‖sigmaHat σ (n : ℤ)‖ ^ 2
      ≤ ‖F‖ ^ 2 * (((N : ℝ) + 1) / N) * (((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), φ n) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hterm : ∀ n ∈ Finset.Icc 1 N, ‖sigmaHat σ (n : ℤ)‖ ^ 2 ≤ ‖F‖ ^ 2 * φ n := by
      intro n _
      calc ‖sigmaHat σ (n : ℤ)‖ ^ 2 = ‖sigmaHat σ (n : ℤ)‖ * ‖sigmaHat σ (n : ℤ)‖ := sq _
        _ ≤ ‖F‖ ^ 2 * φ n := by
            refine mul_le_mul (hbound2 n) (hbound n) (norm_nonneg _) (by positivity)
    have hsum : ∑ n ∈ Finset.Icc 1 N, ‖sigmaHat σ (n : ℤ)‖ ^ 2
        ≤ ‖F‖ ^ 2 * ∑ n ∈ Finset.range (N + 1), φ n := by
      calc ∑ n ∈ Finset.Icc 1 N, ‖sigmaHat σ (n : ℤ)‖ ^ 2
          ≤ ∑ n ∈ Finset.Icc 1 N, ‖F‖ ^ 2 * φ n := Finset.sum_le_sum hterm
        _ = ‖F‖ ^ 2 * ∑ n ∈ Finset.Icc 1 N, φ n := by rw [Finset.mul_sum]
        _ ≤ ‖F‖ ^ 2 * ∑ n ∈ Finset.range (N + 1), φ n := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => hφnn n
            intro n hn
            simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
            omega
    rw [show ‖F‖ ^ 2 * (((N : ℝ) + 1) / N) * (((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), φ n)
        = (N : ℝ)⁻¹ * (‖F‖ ^ 2 * ∑ n ∈ Finset.range (N + 1), φ n) by
      field_simp]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  -- The dominating sequence tends to `0`.
  have hA := tendsto_cesaro_integral_abs_condInner D hm hb hcwm
  have hA' : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), φ n)
      Filter.atTop (nhds 0) := by
    have hcomp := hA.comp (Filter.tendsto_add_atTop_nat 1)
    refine hcomp.congr fun N => ?_
    simp only [Function.comp_def, hφ]
    push_cast
    ring_nf
  have hratio : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1) / N) Filter.atTop (nhds 1) := by
    have : ∀ N : ℕ, 0 < N → ((N : ℝ) + 1) / N = 1 + (N : ℝ)⁻¹ := by
      intro N hN
      have : (N : ℝ) ≠ 0 := by positivity
      field_simp
    refine Filter.Tendsto.congr' ?_ (by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN using (this N hN).symm
  have hprod : Filter.Tendsto
      (fun N : ℕ => ‖F‖ ^ 2 * (((N : ℝ) + 1) / N)
        * (((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), φ n))
      Filter.atTop (nhds 0) := by
    have := ((tendsto_const_nhds (x := ‖F‖ ^ 2)).mul hratio).mul hA'
    simpa using this
  -- Squeeze and apply Wiener.
  have : IsFiniteMeasure σ := hspec.isFinite
  refine noAtoms_of_tendsto_cesaro_zero ?_
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => ?_)
    (Filter.Eventually.of_forall hdom) hprod
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => by positivity)

end MPS

end CantorSzemeredi

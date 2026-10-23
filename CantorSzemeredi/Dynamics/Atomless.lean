/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.Koopman
import CantorSzemeredi.Dynamics.Extensions
import CantorSzemeredi.Dynamics.SpectralExists
import CantorSzemeredi.Dynamics.Joining

/-!
# Conditional weak mixing gives atomless spectral measures

Blueprint: `lem:atomless` in `blueprint/src/chapter/mps.tex`, part (i).

If `f` is conditionally weakly mixing then its spectral measure, for the Koopman operator of
`T`, has no atoms.  The chain is: the Fourier coefficients of `σ_f` are the correlations
`⟪f, Uⁿ f⟫`; those are integrals of `⟨Tⁿ f, f⟩_{E|D}`, so bounded by its `L¹(D)` norm;
conditional weak mixing makes the Cesàro means of those norms vanish; and Wiener's lemma
turns that into the absence of atoms.

## State

Both parts are proved: `noAtoms_specMeasure_of_condWeaklyMixing` (i) and
`noAtoms_specMeasure_prod_of_condWeaklyMixing` (ii), the latter on the product system
`prodSystem D = (X × X, λ, T × T)`.  The identity `eq:psi-identity` is
`integral_tensorSq_comp`.
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

/-! ### Part (ii): the product system

`G = f ⊗ f` on `L²(λ)`, where `λ` is the relatively independent self-joining and the
transformation is `R = T × T`.  The identity `eq:psi-identity` says that the correlations of
`G` are the squared `L²(D)` norms of the conditional correlations of `f`; it is `eq:joining`
applied to `a = a' = f · (f ∘ Tⁿ)`.
-/

variable [StandardBorelSpace S.X]

omit [StandardBorelSpace S.X] in
/-- `|E(g|D)| ≤ K` almost everywhere when `|g| ≤ K`. -/
theorem abs_condExp_le (D : Factor S) {g : S.X → ℝ} {K : ℝ} (hg : Integrable g S.m)
    (hK : ∀ x, |g x| ≤ K) : ∀ᵐ x ∂S.m, |(S.m[g|D.σ]) x| ≤ K := by
  have hub : (S.m[g|D.σ]) ≤ᵐ[S.m] fun _ => K := by
    have h := condExp_mono (m := D.σ) hg (integrable_const K)
      (Filter.Eventually.of_forall fun x => le_trans (le_abs_self _) (hK x))
    rw [condExp_const (μ := S.m) (m := D.σ) D.le K] at h
    exact h
  have hlb : (fun _ => -K) ≤ᵐ[S.m] (S.m[g|D.σ]) := by
    have h := condExp_mono (m := D.σ) (integrable_const (-K)) hg
      (Filter.Eventually.of_forall fun x => by
        have := hK x
        rw [abs_le] at this
        exact this.1)
    rw [condExp_const (μ := S.m) (m := D.σ) D.le (-K)] at h
    exact h
  filter_upwards [hub, hlb] with x hx hx'
  rw [abs_le]
  exact ⟨hx', hx⟩

/-- `G = f ⊗ f` as a bounded measurable function on `X × X`. -/
noncomputable def tensorSq (f : S.X → ℝ) : S.X × S.X → ℝ := fun p => f p.1 * f p.2

omit [StandardBorelSpace S.X] in
theorem measurable_tensorSq {f : S.X → ℝ} (hm : Measurable f) : Measurable (tensorSq f) :=
  (hm.comp measurable_fst).mul (hm.comp measurable_snd)

omit [StandardBorelSpace S.X] in
theorem abs_tensorSq_le {f : S.X → ℝ} {C : ℝ} (hb : ∀ x, |f x| ≤ C) (p : S.X × S.X) :
    |tensorSq f p| ≤ C * C := by
  have h₀ : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hb p.1)
  rw [tensorSq, abs_mul]
  exact mul_le_mul (hb _) (hb _) (abs_nonneg _) h₀

/-- **Equation `eq:psi-identity`.**  The correlations of `G = f ⊗ f` under `R = T × T` are the
squared `L²(D)` norms of the conditional correlations of `f`. -/
theorem integral_tensorSq_comp (D : Factor S) {f : S.X → ℝ} {C : ℝ}
    (hm : Measurable f) (hb : ∀ x, |f x| ≤ C) (n : ℕ) :
    ∫ p, tensorSq f p * tensorSq f ((prodMap S)^[n] p) ∂(joining D)
      = ∫ x, (condInner D (f ∘ S.T^[n]) f x) ^ 2 ∂S.m := by
  classical
  set a : S.X → ℝ := fun x => f x * f (S.T^[n] x) with ha
  have hmeas : Measurable a := hm.mul (hm.comp (S.measurable_T.iterate n))
  have hbnd : ∀ x, |a x| ≤ C * C := by
    intro x
    have h₀ : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hb x)
    rw [ha, abs_mul]
    exact mul_le_mul (hb _) (hb _) (abs_nonneg _) h₀
  -- The integrand is the tensor `a ⊗ a`.
  have hint : (fun p : S.X × S.X => tensorSq f p * tensorSq f ((prodMap S)^[n] p))
      = fun p : S.X × S.X => a p.1 * a p.2 := by
    funext p
    rw [tensorSq, tensorSq, prodMap_iterate, ha]
    ring
  rw [hint, integral_joining D hmeas hmeas hbnd hbnd]
  refine integral_congr_ae ?_
  filter_upwards with x
  have hcond : (S.m[a|D.σ]) x = condInner D (f ∘ S.T^[n]) f x := by
    rw [condInner]
    congr 1
    funext y
    simp [ha, mul_comm]
  rw [hcond, sq]

/-- **Lemma `lem:atomless`(ii).**  For conditionally weakly mixing `f`, the spectral measure
of `G = f ⊗ f` for the Koopman operator of `R = T × T` on `L²(λ)` has no atoms. -/
theorem noAtoms_specMeasure_prod_of_condWeaklyMixing (D : Factor S) {f : S.X → ℝ} {C : ℝ}
    (hm : Measurable f) (hb : ∀ x, |f x| ≤ C) (hcwm : CondWeaklyMixing D f) :
    ∀ θ : Torus, specMeasure (prodSystem D).koopman
      (toLpC (prodSystem D) (measurable_tensorSq hm) (abs_tensorSq_le hb)) {θ} = 0 := by
  set P := prodSystem D with hP
  set G := toLpC P (measurable_tensorSq hm) (abs_tensorSq_le hb) with hG
  set σ := specMeasure P.koopman G with hσ
  have hspec := hasSpectralMeasure_specMeasure P.koopman G
  have : IsFiniteMeasure σ := hspec.isFinite
  set ψ : ℕ → ℝ := fun n => ∫ x, (condInner D (f ∘ S.T^[n]) f x) ^ 2 ∂S.m with hψ
  set φ : ℕ → ℝ := fun n => ∫ x, |condInner D (f ∘ S.T^[n]) f x| ∂S.m with hφ
  have hψnn : ∀ n, 0 ≤ ψ n := fun n => integral_nonneg fun x => sq_nonneg _
  -- The Fourier coefficients of `σ` are the `ψ n`.
  have hcoeff : ∀ n : ℕ, sigmaHat σ (n : ℤ) = ((ψ n : ℝ) : ℂ) := by
    intro n
    rw [sigmaHat, ← hspec.inner_eq (n : ℤ),
      inner_toLpC (S := P) (measurable_tensorSq hm) (abs_tensorSq_le hb) n, hψ]
    congr 1
    exact integral_tensorSq_comp D hm hb n
  -- `ψ n ≤ C² φ n`, by the pointwise bound on the conditional correlation.
  have hbound : ∀ n : ℕ, ψ n ≤ (C * C) * φ n := by
    intro n
    have hprodint : Integrable ((f ∘ S.T^[n]) * f) S.m := by
      refine MemLp.integrable (q := ⊤) le_top ?_
      refine memLp_top_of_bound
        (((hm.comp (S.measurable_T.iterate n)).mul hm).aestronglyMeasurable) (C * C) ?_
      filter_upwards with x
      have h₀ : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hb x)
      simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hb _) (hb _) (abs_nonneg _) h₀
    have hptw : ∀ᵐ x ∂S.m, |condInner D (f ∘ S.T^[n]) f x| ≤ C * C := by
      refine abs_condExp_le D hprodint ?_
      intro x
      have h₀ : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hb x)
      simp only [Pi.mul_apply, Function.comp_apply, abs_mul]
      exact mul_le_mul (hb _) (hb _) (abs_nonneg _) h₀
    have hsqint : Integrable (fun x => (condInner D (f ∘ S.T^[n]) f x) ^ 2) S.m := by
      refine MemLp.integrable (q := ⊤) le_top ?_
      have hsm : StronglyMeasurable fun x => (condInner D (f ∘ S.T^[n]) f x) ^ 2 :=
        (stronglyMeasurable_condExp.mono D.le).pow 2
      refine memLp_top_of_bound hsm.aestronglyMeasurable ((C * C) * (C * C)) ?_
      filter_upwards [hptw] with x hx
      rw [Real.norm_eq_abs, abs_pow, sq]
      have h₀ : (0 : ℝ) ≤ |condInner D (f ∘ S.T^[n]) f x| := abs_nonneg _
      exact mul_le_mul hx hx h₀ (by nlinarith [h₀, hx])
    rw [hψ, hφ, ← integral_const_mul]
    refine integral_mono_ae hsqint ?_ ?_
    · exact (integrable_abs_condInner D hm hb n).const_mul _
    · filter_upwards [hptw] with x hx
      rw [sq]
      rcases abs_cases (condInner D (f ∘ S.T^[n]) f x) with ⟨he, _⟩ | ⟨he, _⟩ <;> nlinarith [hx,
        abs_nonneg (condInner D (f ∘ S.T^[n]) f x)]
  -- The Cesàro means of `‖σ̂(n)‖²` vanish, so Wiener applies.
  have hA := tendsto_cesaro_integral_abs_condInner D hm hb hcwm
  have hsqbound : ∀ n : ℕ, ‖sigmaHat σ (n : ℤ)‖ ^ 2 ≤ (‖G‖ ^ 2 * (C * C)) * φ n := by
    intro n
    have hnorm : ‖sigmaHat σ (n : ℤ)‖ ≤ ‖G‖ ^ 2 := by
      rw [sigmaHat, ← hspec.inner_eq (n : ℤ)]
      calc ‖(inner ℂ G ((P.koopman ^ (n : ℤ)) G) : ℂ)‖
          ≤ ‖G‖ * ‖(P.koopman ^ (n : ℤ)) G‖ := norm_inner_le_norm _ _
        _ = ‖G‖ ^ 2 := by rw [LinearIsometryEquiv.norm_map]; ring
    have hψbound : ‖sigmaHat σ (n : ℤ)‖ ≤ (C * C) * φ n := by
      rw [hcoeff n, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψnn n)]
      exact hbound n
    calc ‖sigmaHat σ (n : ℤ)‖ ^ 2 = ‖sigmaHat σ (n : ℤ)‖ * ‖sigmaHat σ (n : ℤ)‖ := sq _
      _ ≤ (‖G‖ ^ 2) * ((C * C) * φ n) :=
          mul_le_mul hnorm hψbound (norm_nonneg _) (by positivity)
      _ = (‖G‖ ^ 2 * (C * C)) * φ n := by ring
  have hdom : ∀ N : ℕ, (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ‖sigmaHat σ (n : ℤ)‖ ^ 2
      ≤ (‖G‖ ^ 2 * (C * C)) * (((N : ℝ) + 1) / N)
        * (((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), φ n) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hK : (0 : ℝ) ≤ ‖G‖ ^ 2 * (C * C) := by
      have h₀ : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hb Classical.ofNonempty)
      positivity
    have hsum : ∑ n ∈ Finset.Icc 1 N, ‖sigmaHat σ (n : ℤ)‖ ^ 2
        ≤ (‖G‖ ^ 2 * (C * C)) * ∑ n ∈ Finset.range (N + 1), φ n := by
      calc ∑ n ∈ Finset.Icc 1 N, ‖sigmaHat σ (n : ℤ)‖ ^ 2
          ≤ ∑ n ∈ Finset.Icc 1 N, (‖G‖ ^ 2 * (C * C)) * φ n :=
            Finset.sum_le_sum fun n _ => hsqbound n
        _ = (‖G‖ ^ 2 * (C * C)) * ∑ n ∈ Finset.Icc 1 N, φ n := by rw [Finset.mul_sum]
        _ ≤ (‖G‖ ^ 2 * (C * C)) * ∑ n ∈ Finset.range (N + 1), φ n := by
            refine mul_le_mul_of_nonneg_left ?_ hK
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_
              fun n _ _ => integral_nonneg fun x => abs_nonneg _
            intro n hn
            simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
            omega
    rw [show (‖G‖ ^ 2 * (C * C)) * (((N : ℝ) + 1) / N)
        * (((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), φ n)
        = (N : ℝ)⁻¹ * ((‖G‖ ^ 2 * (C * C)) * ∑ n ∈ Finset.range (N + 1), φ n) by field_simp]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hA' : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), φ n)
      Filter.atTop (nhds 0) := by
    have hcomp := hA.comp (Filter.tendsto_add_atTop_nat 1)
    refine hcomp.congr fun N => ?_
    simp only [Function.comp_def, hφ]
    push_cast
    ring_nf
  have hratio : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1) / N) Filter.atTop (nhds 1) := by
    have hform : ∀ N : ℕ, 0 < N → ((N : ℝ) + 1) / N = 1 + (N : ℝ)⁻¹ := by
      intro N hN
      have : (N : ℝ) ≠ 0 := by positivity
      field_simp
    refine Filter.Tendsto.congr' ?_ (by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN using (hform N hN).symm
  have hprod : Filter.Tendsto
      (fun N : ℕ => (‖G‖ ^ 2 * (C * C)) * (((N : ℝ) + 1) / N)
        * (((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), φ n))
      Filter.atTop (nhds 0) := by
    have := ((tendsto_const_nhds (x := ‖G‖ ^ 2 * (C * C))).mul hratio).mul hA'
    simpa using this
  refine noAtoms_of_tendsto_cesaro_zero ?_
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => ?_)
    (Filter.Eventually.of_forall hdom) hprod
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => by positivity)

/-! ### Towards `lem:dichotomy`

The first step of the Furstenberg dichotomy: if `f` is **not** conditionally weakly mixing,
then the spectral measure of `G = f ⊗ f` has an atom.  This is the converse of part (ii),
and it is where the dichotomy's compact extension will eventually come from.

The measure-theoretic half is done: `exists_atom_of_not_tendsto_cesaro_zero` turns a
non-vanishing Cesàro mean into an atom, and `integral_tensorSq_comp` identifies the Fourier
coefficients of `σ_G` with `ψ(n) = ‖⟨Tⁿf,f⟩_{E|D}‖²_{L²(D)}`.

What is missing to complete the step is the converse of the estimate used in part (ii): that
vanishing Cesàro means of `ψ` give conditional weak mixing, i.e.
`‖E_N u_n‖_{L²} ≤ E_N ‖u_n‖_{L²} ≤ √(E_N ψ n)` by the triangle inequality and
Cauchy–Schwarz.  In Lean that needs `eLpNorm`-level API (the `L²` norm of a finite sum, and
`∫ g² = ‖g‖²_{L²}`) that Mathlib does not provide in directly usable form.

Even with that step, the dichotomy itself would remain: see the blueprint's remark on
`lem:dichotomy`, which scopes it as a project of its own.
-/

end MPS

end CantorSzemeredi

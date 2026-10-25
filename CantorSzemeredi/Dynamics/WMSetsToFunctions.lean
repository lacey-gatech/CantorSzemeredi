/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMMainFinal
import CantorSzemeredi.Dynamics.Extensions
import CantorSzemeredi.Dynamics.CompactSystem

/-!
# From sets to functions

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-sets-to-functions`.  For a weakly mixing
system the set-theoretic mixing of indicators implies the Cesàro mixing of all `L²` functions,
and hence that the trivial factor is a weakly mixing extension of the top factor.

The proof follows the blueprint: indicators, then simple functions by bilinearity (proved by
`SimpleFunc.induction`), then `L²` functions by density, using measure preservation and
Cauchy–Schwarz.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Filter Topology

namespace MPS

variable {S : MPS.{0}}

/-- The correlation `c_n(f,g) = ∫ f∘Tⁿ · g − ∫f ∫g`. -/
noncomputable def corrF (S : MPS.{0}) (f g : S.X → ℝ) (n : ℕ) : ℝ :=
  ∫ x, f (S.T^[n] x) * g x ∂S.m - (∫ x, f x ∂S.m) * (∫ x, g x ∂S.m)

/-- Bounded measurable functions. -/
def BddMeas (f : S.X → ℝ) : Prop :=
  Measurable f ∧ ∃ K : ℝ, ∀ x, |f x| ≤ K

theorem BddMeas.integrable {f : S.X → ℝ} (hf : BddMeas f) : Integrable f S.m := by
  obtain ⟨hm, K, hK⟩ := hf
  exact integrable_of_bdd_const hm hK

theorem BddMeas.comp_iter {f : S.X → ℝ} (hf : BddMeas f) (n : ℕ) :
    BddMeas (fun x => f (S.T^[n] x)) := by
  obtain ⟨hm, K, hK⟩ := hf
  exact ⟨hm.comp (S.measurable_T.iterate n), K, fun x => hK _⟩

theorem BddMeas.mul {f g : S.X → ℝ} (hf : BddMeas f) (hg : BddMeas g) :
    BddMeas (fun x => f x * g x) := by
  obtain ⟨hm, K, hK⟩ := hf
  obtain ⟨hm', L, hL⟩ := hg
  refine ⟨hm.mul hm', K * L, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hK x) (hL x) (abs_nonneg _) (le_trans (abs_nonneg _) (hK x))

theorem BddMeas.integrable_mul {f g : S.X → ℝ} (hf : BddMeas f) (hg : BddMeas g) :
    Integrable (fun x => f x * g x) S.m :=
  (hf.mul hg).integrable

/-- The correlation is additive in the first argument. -/
theorem corrF_add_left {f₁ f₂ g : S.X → ℝ} (h₁ : BddMeas f₁) (h₂ : BddMeas f₂) (hg : BddMeas g)
    (n : ℕ) : corrF S (fun x => f₁ x + f₂ x) g n = corrF S f₁ g n + corrF S f₂ g n := by
  unfold corrF
  have hI : ∀ f : S.X → ℝ, BddMeas f → Integrable (fun x => f (S.T^[n] x) * g x) S.m :=
    fun f hf => (hf.comp_iter n).integrable_mul hg
  simp only [add_mul]
  rw [integral_add (hI f₁ h₁) (hI f₂ h₂), integral_add h₁.integrable h₂.integrable]
  ring

/-- The correlation is additive in the second argument. -/
theorem corrF_add_right {f g₁ g₂ : S.X → ℝ} (hf : BddMeas f) (h₁ : BddMeas g₁) (h₂ : BddMeas g₂)
    (n : ℕ) : corrF S f (fun x => g₁ x + g₂ x) n = corrF S f g₁ n + corrF S f g₂ n := by
  unfold corrF
  have hI : ∀ g : S.X → ℝ, BddMeas g → Integrable (fun x => f (S.T^[n] x) * g x) S.m :=
    fun g hg => (hf.comp_iter n).integrable_mul hg
  simp only [mul_add]
  rw [integral_add (hI g₁ h₁) (hI g₂ h₂), integral_add h₁.integrable h₂.integrable]
  ring

/-- The correlation is homogeneous in the first argument. -/
theorem corrF_smul_left (c : ℝ) (f g : S.X → ℝ) (n : ℕ) :
    corrF S (fun x => c * f x) g n = c * corrF S f g n := by
  unfold corrF
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul]
  ring

/-- The correlation is homogeneous in the second argument. -/
theorem corrF_smul_right (c : ℝ) (f g : S.X → ℝ) (n : ℕ) :
    corrF S f (fun x => c * g x) n = c * corrF S f g n := by
  unfold corrF
  have : ∀ x, f (S.T^[n] x) * (c * g x) = c * (f (S.T^[n] x) * g x) := fun x => by ring
  simp only [this]
  rw [integral_const_mul, integral_const_mul]
  ring

/-- For indicators, the correlation is the measure of `B ∩ T^{-n} A`. -/
theorem corrF_indicator (A B : Set S.X) (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    corrF S (A.indicator 1) (B.indicator 1) n
      = (S.m (B ∩ S.T^[n] ⁻¹' A)).toReal - (S.m A).toReal * (S.m B).toReal := by
  unfold corrF
  have hprod : (fun x => A.indicator (1 : S.X → ℝ) (S.T^[n] x) * B.indicator 1 x)
      = (B ∩ S.T^[n] ⁻¹' A).indicator 1 := by
    funext x
    simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, Pi.one_apply]
    by_cases h1 : S.T^[n] x ∈ A <;> by_cases h2 : x ∈ B <;> simp [h1, h2]
  rw [hprod, integral_indicator_one (hB.inter (S.measurable_T.iterate n hA)),
    integral_indicator_one hA, integral_indicator_one hB]
  simp only [measureReal_def]

/-- The Cesàro averages of `|c_n(f,g)|` tend to zero. -/
def CesaroTo0 (f g : S.X → ℝ) : Prop :=
  Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S f g n|) atTop (𝓝 0)

/-- Indicators of measurable sets: this is the set-theoretic weak mixing. -/
theorem cesaroTo0_indicator (hWM : S.WeaklyMixing) {A B : Set S.X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) : CesaroTo0 (A.indicator 1) (B.indicator 1) := by
  have h := hWM B A hB hA
  unfold CesaroTo0
  refine h.congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [corrF_indicator A B hA hB n, mul_comm]

theorem cesaroTo0_smul {f g : S.X → ℝ} (c d : ℝ) (h : CesaroTo0 f g) :
    CesaroTo0 (fun x => c * f x) (fun x => d * g x) := by
  unfold CesaroTo0 at *
  have hcorr : ∀ n, |corrF S (fun x => c * f x) (fun x => d * g x) n|
      = |c * d| * |corrF S f g n| := fun n => by
    simp only [corrF_smul_left, corrF_smul_right, abs_mul]
    ring
  simp_rw [hcorr]
  have := h.const_mul |c * d|
  rw [mul_zero] at this
  refine this.congr fun N => ?_
  rw [← Finset.mul_sum]
  ring

theorem cesaroTo0_add_left {f₁ f₂ g : S.X → ℝ} (h₁ : BddMeas f₁) (h₂ : BddMeas f₂)
    (hg : BddMeas g) (c₁ : CesaroTo0 f₁ g) (c₂ : CesaroTo0 f₂ g) :
    CesaroTo0 (fun x => f₁ x + f₂ x) g := by
  unfold CesaroTo0 at *
  have hle : ∀ N : ℕ, (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S (fun x => f₁ x + f₂ x) g n|
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S f₁ g n|
        + (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S f₂ g n| := fun N => by
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) (by positivity)
    rw [corrF_add_left h₁ h₂ hg n]
    exact abs_add_le _ _
  have hsum := c₁.add c₂
  rw [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun N => by
      have : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
      exact mul_nonneg this (Finset.sum_nonneg fun n _ => abs_nonneg _))
    hle

theorem cesaroTo0_add_right {f g₁ g₂ : S.X → ℝ} (hf : BddMeas f) (h₁ : BddMeas g₁)
    (h₂ : BddMeas g₂) (c₁ : CesaroTo0 f g₁) (c₂ : CesaroTo0 f g₂) :
    CesaroTo0 f (fun x => g₁ x + g₂ x) := by
  unfold CesaroTo0 at *
  have hle : ∀ N : ℕ, (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S f (fun x => g₁ x + g₂ x) n|
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S f g₁ n|
        + (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S f g₂ n| := fun N => by
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) (by positivity)
    rw [corrF_add_right hf h₁ h₂ n]
    exact abs_add_le _ _
  have hsum := c₁.add c₂
  rw [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun N => by
      have : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
      exact mul_nonneg this (Finset.sum_nonneg fun n _ => abs_nonneg _))
    hle

/-- Simple functions are bounded and measurable. -/
theorem bddMeas_simple (s : SimpleFunc S.X ℝ) : BddMeas (⇑s) :=
  ⟨s.measurable, ∑ y ∈ s.range, |y|, fun x =>
    Finset.single_le_sum (f := fun y => |y|) (fun y _ => abs_nonneg y)
      (SimpleFunc.mem_range_self s x) |> fun h => by simpa using h⟩

/-- The indicator-valued simple function `c · 1_A`. -/
theorem coe_piecewise_const_eq (A : Set S.X) (hA : MeasurableSet A) (c : ℝ) :
    ⇑(SimpleFunc.piecewise A hA (SimpleFunc.const _ c) (SimpleFunc.const _ 0))
      = fun x => c * A.indicator 1 x := by
  funext x
  by_cases hx : x ∈ A
  · simp [SimpleFunc.coe_piecewise, hx]
  · simp [SimpleFunc.coe_piecewise, Set.indicator_of_notMem hx, hx]

/-- **Simple functions.**  For weakly mixing `S`, every pair of simple functions has Cesàro-mixing
correlations. -/
theorem cesaroTo0_simple (hWM : S.WeaklyMixing) (s : SimpleFunc S.X ℝ) :
    ∀ t : SimpleFunc S.X ℝ, CesaroTo0 (⇑s) (⇑t) := by
  induction s using SimpleFunc.induction with
  | const c hs =>
    intro t
    rw [coe_piecewise_const_eq _ hs c]
    induction t using SimpleFunc.induction with
    | const d hB =>
      rw [coe_piecewise_const_eq _ hB d]
      exact cesaroTo0_smul c d (cesaroTo0_indicator hWM hs hB)
    | add hdisj ihf ihg =>
      rw [SimpleFunc.coe_add]
      have hb := bddMeas_simple (SimpleFunc.piecewise _ hs (SimpleFunc.const _ c)
        (SimpleFunc.const _ 0))
      rw [coe_piecewise_const_eq _ hs c] at hb
      exact cesaroTo0_add_right hb (bddMeas_simple _) (bddMeas_simple _) ihf ihg
  | add hdisj ihf ihg =>
    intro t
    rw [SimpleFunc.coe_add]
    exact cesaroTo0_add_left (bddMeas_simple _) (bddMeas_simple _) (bddMeas_simple t)
      (ihf t) (ihg t)

/-- The `L²` norm of a real function, as a real number. -/
noncomputable def N2 (f : S.X → ℝ) : ℝ := (eLpNorm f 2 S.m).toReal

theorem N2_nonneg (f : S.X → ℝ) : 0 ≤ N2 f := ENNReal.toReal_nonneg

theorem norm_toLp_eq {u : S.X → ℝ} (hu : MemLp u 2 S.m) : ‖hu.toLp u‖ = N2 u := by
  unfold N2
  rw [Lp.norm_def]
  congr 1
  exact eLpNorm_congr_ae hu.coeFn_toLp

/-- Cauchy–Schwarz for the integral of a product of `L²` functions. -/
theorem abs_integral_mul_le_N2 {u v : S.X → ℝ} (hu : MemLp u 2 S.m) (hv : MemLp v 2 S.m) :
    |∫ x, u x * v x ∂S.m| ≤ N2 u * N2 v := by
  have hinner : inner ℝ (hu.toLp u) (hv.toLp v) = ∫ x, u x * v x ∂S.m := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x h1 h2
    simp [h1, h2, RCLike.inner_apply, mul_comm]
  rw [← hinner, ← norm_toLp_eq hu, ← norm_toLp_eq hv]
  exact abs_real_inner_le_norm _ _

/-- The `L¹` norm of an `L²` function is bounded by its `L²` norm, on a probability space. -/
theorem abs_integral_le_N2 {u : S.X → ℝ} (hu : MemLp u 2 S.m) :
    |∫ x, u x ∂S.m| ≤ N2 u := by
  have h1 : MemLp (fun _ : S.X => (1 : ℝ)) 2 S.m := memLp_const 1
  have hN1 : N2 (fun _ : S.X => (1 : ℝ)) = 1 := by
    unfold N2
    rw [eLpNorm_const (1 : ℝ) (by norm_num) (NeZero.ne S.m)]
    simp
  have := abs_integral_mul_le_N2 hu h1
  simpa [hN1] using this

/-- Triangle inequality for `N2`. -/
theorem N2_sub_le {u v : S.X → ℝ} (hu : MemLp u 2 S.m) (hv : MemLp v 2 S.m) :
    N2 (fun x => u x - v x) ≤ N2 u + N2 v := by
  unfold N2
  have hle : eLpNorm (fun x => u x - v x) 2 S.m ≤ eLpNorm u 2 S.m + eLpNorm v 2 S.m :=
    eLpNorm_sub_le (μ := S.m) (f := u) (g := v) (by norm_num)
  have hfin1 : eLpNorm u 2 S.m ≠ ⊤ := hu.eLpNorm_ne_top
  have hfin2 : eLpNorm v 2 S.m ≠ ⊤ := hv.eLpNorm_ne_top
  rw [← ENNReal.toReal_add hfin1 hfin2]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩) hle

/-- The `L²` norm is invariant under the iterates of `T`. -/
theorem N2_comp_iter (u : S.X → ℝ) (hu : AEStronglyMeasurable u S.m) (n : ℕ) :
    N2 (fun x => u (S.T^[n] x)) = N2 u := by
  unfold N2
  have h := eLpNorm_comp_measurePreserving (p := 2) hu (S.measurePreserving_T_iterate n)
  exact congrArg ENNReal.toReal h

/-- The difference of correlations, split into two Cauchy–Schwarz terms. -/
theorem abs_corr_integral_sub_le {u v u' v' : S.X → ℝ} (hu : MemLp u 2 S.m) (hv : MemLp v 2 S.m)
    (hu' : MemLp u' 2 S.m) (hv' : MemLp v' 2 S.m) (n : ℕ) :
    |∫ x, u (S.T^[n] x) * v x ∂S.m - ∫ x, u' (S.T^[n] x) * v' x ∂S.m|
      ≤ N2 (fun x => u x - u' x) * N2 v + N2 u' * N2 (fun x => v x - v' x) := by
  have hcomp : ∀ w : S.X → ℝ, MemLp w 2 S.m → MemLp (fun x => w (S.T^[n] x)) 2 S.m :=
    fun w hw => hw.comp_measurePreserving (S.measurePreserving_T_iterate n)
  have huu : MemLp (fun x => u x - u' x) 2 S.m := hu.sub hu'
  have hvv : MemLp (fun x => v x - v' x) 2 S.m := hv.sub hv'
  have hA : Integrable (fun x => u (S.T^[n] x) * v x) S.m :=
    (hcomp u hu).integrable_mul hv
  have hB : Integrable (fun x => u' (S.T^[n] x) * v' x) S.m :=
    (hcomp u' hu').integrable_mul hv'
  have hC : Integrable (fun x => (fun y => u y - u' y) (S.T^[n] x) * v x) S.m :=
    (hcomp _ huu).integrable_mul hv
  have hD : Integrable (fun x => u' (S.T^[n] x) * (fun y => v y - v' y) x) S.m :=
    (hcomp u' hu').integrable_mul hvv
  have hsplit : ∫ x, u (S.T^[n] x) * v x ∂S.m - ∫ x, u' (S.T^[n] x) * v' x ∂S.m
      = ∫ x, (fun y => u y - u' y) (S.T^[n] x) * v x ∂S.m
        + ∫ x, u' (S.T^[n] x) * (fun y => v y - v' y) x ∂S.m := by
    rw [← integral_sub hA hB, ← integral_add hC hD]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hsplit]
  have hC' : |∫ x, (fun y => u y - u' y) (S.T^[n] x) * v x ∂S.m|
      ≤ N2 (fun x => u x - u' x) * N2 v := by
    have h := abs_integral_mul_le_N2 (hcomp _ huu) hv
    have hcomp_N2 := N2_comp_iter (fun x => u x - u' x) huu.aestronglyMeasurable n
    rw [hcomp_N2] at h
    exact h
  have hD' : |∫ x, u' (S.T^[n] x) * (fun y => v y - v' y) x ∂S.m|
      ≤ N2 u' * N2 (fun x => v x - v' x) := by
    have h := abs_integral_mul_le_N2 (hcomp u' hu') hvv
    have hcomp_N2 := N2_comp_iter u' hu'.aestronglyMeasurable n
    rw [hcomp_N2] at h
    exact h
  exact le_trans (abs_add_le _ _) (add_le_add hC' hD')

/-- The difference of means, split into two Cauchy–Schwarz terms. -/
theorem abs_mean_sub_le {u v u' v' : S.X → ℝ} (hu : MemLp u 2 S.m) (hv : MemLp v 2 S.m)
    (hu' : MemLp u' 2 S.m) (hv' : MemLp v' 2 S.m) :
    |(∫ x, u x ∂S.m) * (∫ x, v x ∂S.m) - (∫ x, u' x ∂S.m) * (∫ x, v' x ∂S.m)|
      ≤ N2 (fun x => u x - u' x) * N2 v + N2 u' * N2 (fun x => v x - v' x) := by
  have huu : MemLp (fun x => u x - u' x) 2 S.m := hu.sub hu'
  have hvv : MemLp (fun x => v x - v' x) 2 S.m := hv.sub hv'
  have e : (∫ x, u x ∂S.m) * (∫ x, v x ∂S.m) - (∫ x, u' x ∂S.m) * (∫ x, v' x ∂S.m)
      = (∫ x, (u x - u' x) ∂S.m) * (∫ x, v x ∂S.m)
        + (∫ x, u' x ∂S.m) * (∫ x, (v x - v' x) ∂S.m) := by
    rw [integral_sub (hu.integrable (by norm_num)) (hu'.integrable (by norm_num)),
      integral_sub (hv.integrable (by norm_num)) (hv'.integrable (by norm_num))]
    ring
  rw [e]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_mul (abs_integral_le_N2 huu) (abs_integral_le_N2 hv) (abs_nonneg _)
      (N2_nonneg _)
  · rw [abs_mul]
    exact mul_le_mul (abs_integral_le_N2 hu') (abs_integral_le_N2 hvv) (abs_nonneg _)
      (N2_nonneg _)

/-- **Lemma `lem:wm-sets-to-functions`, the `L²` form.**  For a weakly mixing system, the Cesàro
averages of `|c_n(f,g)|` tend to zero for all `f, g ∈ L²`. -/
theorem cesaroTo0_L2 (hWM : S.WeaklyMixing) {f g : S.X → ℝ} (hf : MemLp f 2 S.m)
    (hg : MemLp g 2 S.m) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S f g n|) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set K : ℝ := N2 f + N2 g + 1 with hK
  have hK1 : 1 ≤ K := by
    have := N2_nonneg f
    have := N2_nonneg g
    linarith
  have hKpos : 0 < K := by linarith
  set η : ℝ := min 1 (ε / (8 * K)) with hη
  have hη0 : 0 < η := lt_min one_pos (div_pos hε (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηK : η * K ≤ ε / 8 := by
    have h1 : η ≤ ε / (8 * K) := min_le_right _ _
    calc η * K ≤ ε / (8 * K) * K := mul_le_mul_of_nonneg_right h1 hKpos.le
      _ = ε / 8 := by field_simp
  -- simple approximants of `f` and `g` in `L²`
  obtain ⟨s, hs, hsmem⟩ := hf.exists_simpleFunc_eLpNorm_sub_lt (by norm_num)
    (ENNReal.ofReal_pos.2 hη0).ne'
  obtain ⟨t, ht, htmem⟩ := hg.exists_simpleFunc_eLpNorm_sub_lt (by norm_num)
    (ENNReal.ofReal_pos.2 hη0).ne'
  have hNs : N2 (fun x => f x - s x) ≤ η := ENNReal.toReal_le_of_le_ofReal hη0.le hs.le
  have hNt : N2 (fun x => g x - t x) ≤ η := ENNReal.toReal_le_of_le_ofReal hη0.le ht.le
  have hsf : MemLp (fun x => f x - s x) 2 S.m := hf.sub hsmem
  have hNs_le : N2 (⇑s) ≤ N2 f + η := by
    have h := N2_sub_le hf hsf
    have e : (fun x => f x - (f x - s x)) = ⇑s := by
      funext x
      ring
    rw [e] at h
    linarith
  -- the difference of the correlations is small, uniformly in `n`
  have hest : ∀ n : ℕ, |corrF S f g n - corrF S ⇑s ⇑t n| ≤ ε / 4 := by
    intro n
    have e : corrF S f g n - corrF S ⇑s ⇑t n
        = (∫ x, f (S.T^[n] x) * g x ∂S.m - ∫ x, (⇑s) (S.T^[n] x) * (⇑t) x ∂S.m)
          - ((∫ x, f x ∂S.m) * (∫ x, g x ∂S.m) - (∫ x, (⇑s) x ∂S.m) * (∫ x, (⇑t) x ∂S.m)) := by
      unfold corrF
      ring
    rw [e]
    have h1 := abs_corr_integral_sub_le hf hg hsmem htmem n
    have h2 := abs_mean_sub_le hf hg hsmem htmem
    have hfs : N2 (fun x => f x - ⇑s x) ≤ η := hNs
    have hgt : N2 (fun x => g x - ⇑t x) ≤ η := hNt
    have hN2g := N2_nonneg g
    have hN2s := N2_nonneg (⇑s)
    have hbound : N2 (fun x => f x - ⇑s x) * N2 g + N2 (⇑s) * N2 (fun x => g x - ⇑t x)
        ≤ η * K := by
      have h3 : N2 (fun x => f x - ⇑s x) * N2 g ≤ η * N2 g :=
        mul_le_mul_of_nonneg_right hfs hN2g
      have h4 : N2 (⇑s) * N2 (fun x => g x - ⇑t x) ≤ (N2 f + η) * η :=
        mul_le_mul hNs_le hgt (N2_nonneg _) (by linarith [N2_nonneg f])
      have h5 : η * N2 g + (N2 f + η) * η ≤ η * K := by
        rw [hK]
        nlinarith
      linarith
    have hfin : |(∫ x, f (S.T^[n] x) * g x ∂S.m - ∫ x, (⇑s) (S.T^[n] x) * (⇑t) x ∂S.m)
        - ((∫ x, f x ∂S.m) * (∫ x, g x ∂S.m) - (∫ x, (⇑s) x ∂S.m) * (∫ x, (⇑t) x ∂S.m))|
        ≤ |∫ x, f (S.T^[n] x) * g x ∂S.m - ∫ x, (⇑s) (S.T^[n] x) * (⇑t) x ∂S.m|
          + |(∫ x, f x ∂S.m) * (∫ x, g x ∂S.m) - (∫ x, (⇑s) x ∂S.m) * (∫ x, (⇑t) x ∂S.m)| :=
      abs_sub _ _
    have h6 := le_trans hfin (add_le_add h1 h2)
    linarith
  -- the Cesàro averages of the approximants tend to zero
  have hcst := cesaroTo0_simple hWM s t
  have hev := (Metric.tendsto_nhds.1 hcst) (ε / 2) (by positivity)
  filter_upwards [hev] with N hN
  have hnn : 0 ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S f g n| := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hN ⊢
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, inv_zero, zero_mul, Finset.sum_range_zero]
    linarith
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hsum : ∑ n ∈ range N, |corrF S f g n|
      ≤ ∑ n ∈ range N, (|corrF S ⇑s ⇑t n| + ε / 4) := by
    refine Finset.sum_le_sum fun n _ => ?_
    have h := hest n
    have h' := abs_sub_abs_le_abs_sub (corrF S f g n) (corrF S ⇑s ⇑t n)
    linarith
  have hfinal : (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S f g n|
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S ⇑s ⇑t n| + ε / 4 := by
    calc (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S f g n|
        ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, (|corrF S ⇑s ⇑t n| + ε / 4) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S ⇑s ⇑t n| + ε / 4 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  linarith

/-- **The trivial factor.**  For a mean-zero `L²` function, the conditional correlation over the
trivial factor is the constant `∫ T^n f · f`, and its Cesàro averages tend to zero. -/
theorem condWeaklyMixing_trivial (hWM : S.WeaklyMixing) {f : S.X → ℝ} (hf : MemLp f 2 S.m)
    (hmean : ∫ x, f x ∂S.m = 0) : CondWeaklyMixing (Factor.trivial S) f := by
  unfold CondWeaklyMixing
  have hconst : ∀ n x, condInner (Factor.trivial S) (f ∘ S.T^[n]) f x
      = ∫ y, f (S.T^[n] y) * f y ∂S.m := by
    intro n x
    have h := condExp_bot' (μ := S.m) ((f ∘ S.T^[n]) * f)
    have hbot : S.m[(f ∘ S.T^[n]) * f | ⊥] = fun _ => ∫ y, f (S.T^[n] y) * f y ∂S.m := by
      rw [h]
      funext _
      simp [probReal_univ]
    unfold condInner
    change S.m[(f ∘ S.T^[n]) * f | ⊥] x = _
    rw [hbot]
  have hfun : ∀ N : ℕ, (fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N,
      |condInner (Factor.trivial S) (f ∘ S.T^[n]) f x|)
        = fun _ => (N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S f f n| := by
    intro N
    funext x
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hconst, corrF, hmean, zero_mul, sub_zero]
  have hnorm : ∀ N : ℕ, eLpNorm (fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N,
      |condInner (Factor.trivial S) (f ∘ S.T^[n]) f x|) 2 S.m
        = ‖((N : ℝ)⁻¹ * ∑ n ∈ range N, |corrF S f f n|)‖ₑ := by
    intro N
    rw [hfun N, eLpNorm_const _ (by norm_num) (NeZero.ne _)]
    simp
  simp_rw [hnorm]
  have hc := cesaroTo0_L2 hWM hf hf
  have h := (continuous_enorm.tendsto (0 : ℝ)).comp hc
  rw [enorm_zero] at h
  exact h

/-- **Lemma `lem:wm-sets-to-functions`.**  A weakly mixing system is a weakly mixing extension of the
trivial factor: every mean-zero `L²` function is conditionally weakly mixing. -/
theorem weaklyMixingExtension_of_weaklyMixing (hWM : S.WeaklyMixing) :
    WeaklyMixingExtension (Factor.trivial S) (Factor.top S) := by
  intro f hMM hmean0
  have hint : ∫ x, f x ∂S.m = 0 := by
    obtain ⟨x, hx1, hx2⟩ := (hmean0.and (condExp_bot_ae_eq f)).exists
    have h1 : S.m[f | (Factor.trivial S).σ] x = 0 := hx1
    have h2 : S.m[f | ⊥] x = (S.m.real Set.univ)⁻¹ • ∫ y, f y ∂S.m := hx2
    change S.m[f | ⊥] x = 0 at h1
    rw [h2, probReal_univ, inv_one, one_smul] at h1
    exact h1
  exact condWeaklyMixing_trivial hWM hMM.memLp hint

end MPS

end CantorSzemeredi

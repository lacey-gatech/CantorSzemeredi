/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.UniformErgodic
import CantorSzemeredi.Dynamics.Atomless
import CantorSzemeredi.Dynamics.CondExpFacts

/-!
# The main weak-mixing estimate: the mean-zero case

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`, the case `t = 1`.

For a bounded `g` which is conditionally weakly mixing, the uniform averages of
`g ∘ T^{s k_n}` tend to zero in `L²`.  This is the uniform ergodic theorem applied to the
spectral measure of `g`, which is atomless by `lem:atomless`.  The file first proves the
bridge between the `Lp` averages of the Koopman operator and the real `eLpNorm`s of the averages.
-/

namespace CantorSzemeredi

open MeasureTheory Filter Topology

namespace MPS

variable {S : MPS}

/-- A finite sum of `L²` elements agrees almost everywhere with the pointwise sum. -/
theorem coeFn_finset_sum_lp {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    (s : Finset ι) (F : ι → Lp ℂ 2 μ) :
    (∑ i ∈ s, F i : Lp ℂ 2 μ) =ᵐ[μ] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 μ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

/-- The Koopman power of the `L²`-class of a bounded function is the shifted function. -/
theorem coeFn_koopman_zpow_toLpC {g : S.X → ℝ} {K : ℝ} (hm : Measurable g)
    (hb : ∀ x, |g x| ≤ K) (k : ℤ) :
    ⇑((S.koopman ^ k) (toLpC S hm hb)) =ᵐ[S.m] fun x => ((g (S.iter k x) : ℝ) : ℂ) := by
  filter_upwards [coeFn_koopman_zpow S k (toLpC S hm hb),
    (S.measurePreserving_iter k).quasiMeasurePreserving.ae_eq_comp (coeFn_toLpC hm hb)]
    with x h1 h2
  rw [h1]
  simpa using h2

/-- **The bridge.**  The `eLpNorm` of the real average of `g ∘ T^{s k_n}` is the norm of the
corresponding average of Koopman powers of `g`. -/
theorem eLpNorm_avg_eq_norm {g : S.X → ℝ} {K : ℝ} (hm : Measurable g) (hb : ∀ x, |g x| ≤ K)
    (ι : Finset ℕ) (k : ℕ → ℕ) (c : ℝ) :
    eLpNorm (fun x => (((c * ∑ n ∈ ι, g (S.T^[k n] x)) : ℝ) : ℂ)) 2 S.m
      = ENNReal.ofReal ‖((c : ℂ) • ∑ n ∈ ι, (S.koopman ^ ((k n : ℕ) : ℤ)) (toLpC S hm hb))‖ := by
  set Φ : Lp ℂ 2 S.m := (c : ℂ) • ∑ n ∈ ι, (S.koopman ^ ((k n : ℕ) : ℤ)) (toLpC S hm hb) with hΦ
  have hae : ⇑Φ =ᵐ[S.m] fun x => (((c * ∑ n ∈ ι, g (S.T^[k n] x)) : ℝ) : ℂ) := by
    have h1 := coeFn_finset_sum_lp ι (fun n => (S.koopman ^ ((k n : ℕ) : ℤ)) (toLpC S hm hb))
    have h2 : ∀ᵐ x ∂S.m, ∀ n : ℕ, ⇑((S.koopman ^ ((k n : ℕ) : ℤ)) (toLpC S hm hb)) x
        = ((g (S.T^[k n] x) : ℝ) : ℂ) := by
      rw [ae_all_iff]
      intro n
      filter_upwards [coeFn_koopman_zpow_toLpC (S := S) hm hb ((k n : ℕ) : ℤ)] with x hx
      rw [hx, S.iter_natCast]
    filter_upwards [Lp.coeFn_smul (c : ℂ) (∑ n ∈ ι, (S.koopman ^ ((k n : ℕ) : ℤ)) (toLpC S hm hb)),
      h1, h2] with x hs hsum hall
    rw [hΦ, hs, Pi.smul_apply, hsum, smul_eq_mul]
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun n _ => hall n
  have hfin : eLpNorm (⇑Φ) 2 S.m ≠ ⊤ := (Lp.memLp Φ).eLpNorm_lt_top.ne
  rw [Lp.norm_def Φ, ENNReal.ofReal_toReal hfin]
  exact eLpNorm_congr_ae hae.symm

/-- A measurable function bounded in absolute value by a constant is integrable. -/
theorem integrable_of_bdd_const {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {φ : α → ℝ} (hm : Measurable φ) {K : ℝ} (hb : ∀ x, |φ x| ≤ K) : Integrable φ μ :=
  (integrable_const K).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

/-- The `eLpNorm` of a real function, viewed as a complex function, is unchanged. -/
theorem eLpNorm_ofReal_coe {r : S.X → ℝ} (hr : Measurable r) :
    eLpNorm (fun x => ((r x : ℝ) : ℂ)) 2 S.m = eLpNorm r 2 S.m := by
  have hc : (fun x => ‖((r x : ℝ) : ℂ)‖) = fun x => ‖r x‖ := funext fun x => Complex.norm_real _
  have h1 := eLpNorm_norm (μ := S.m) (p := 2) (fun x => ((r x : ℝ) : ℂ))
    (hr.complex_ofReal.aestronglyMeasurable)
  have h2 := eLpNorm_norm (μ := S.m) (p := 2) r hr.aestronglyMeasurable
  rw [← h1, hc, h2]

/-- **The mean-zero case of `lem:wm-main`.**  A bounded conditionally weakly mixing `g` has
uniform averages of `g ∘ T^{s k_n}` tending to zero in `L²`. -/
theorem tendsto_avg_of_condWeaklyMixing (C : CantorData) {s : ℕ} (hs : 1 ≤ s) {D : Factor S}
    {g : S.X → ℝ} {K : ℝ} (hm : Measurable g) (hb : ∀ x, |g x| ≤ K)
    (hcwm : CondWeaklyMixing D g) :
    Tendsto (fun p : ℕ × ℕ => eLpNorm (fun x => ((p.2 - p.1 : ℕ) : ℝ)⁻¹ *
        ∑ n ∈ Finset.Ico p.1 p.2, g (S.T^[s * C.enum n] x)) 2 S.m) uniformFilter (𝓝 0) := by
  have : NullSingletonClass (specMeasure S.koopman (toLpC S hm hb)) :=
    ⟨fun θ => noAtoms_specMeasure_of_condWeaklyMixing D hm hb hcwm θ⟩
  have hσ := hasSpectralMeasure_specMeasure S.koopman (toLpC S hm hb)
  have hcor := tendsto_uniformAvg_koopman_zero (S := S) C hs hσ
  have hcongr : ∀ p : ℕ × ℕ,
      eLpNorm (fun x => ((p.2 - p.1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.Ico p.1 p.2, g (S.T^[s * C.enum n] x)) 2 S.m
        = ENNReal.ofReal ‖((((p.2 - p.1 : ℕ) : ℂ))⁻¹ •
            ∑ n ∈ Finset.Ico p.1 p.2, (S.koopman ^ ((s * C.enum n : ℕ) : ℤ)) (toLpC S hm hb))‖ := by
    intro p
    have hmeas : Measurable (fun x => ((p.2 - p.1 : ℕ) : ℝ)⁻¹ *
        ∑ n ∈ Finset.Ico p.1 p.2, g (S.T^[s * C.enum n] x)) :=
      measurable_const.mul (Finset.measurable_sum _ fun n _ =>
        hm.comp (S.measurable_T.iterate _))
    rw [← eLpNorm_ofReal_coe hmeas]
    have hc : ((((p.2 - p.1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) = ((p.2 - p.1 : ℕ) : ℂ)⁻¹ := by
      push_cast
      rfl
    have key := eLpNorm_avg_eq_norm (S := S) hm hb (Finset.Ico p.1 p.2) (fun n => s * C.enum n)
      (((p.2 - p.1 : ℕ) : ℝ)⁻¹)
    rw [hc] at key
    exact key
  simp only [hcongr]
  have h0 : ENNReal.ofReal 0 = 0 := by simp
  have := ENNReal.tendsto_ofReal hcor
  rw [h0] at this
  exact this

/-- **The case `t = 1` of `lem:wm-main`.**  Let `D ⊆ E` be factors such that every bounded
`E`-measurable function with `E(f|D) = 0` is conditionally weakly mixing (hypothesis (WM)).
Then for bounded `E`-measurable `f`, the uniform averages of `f ∘ T^{s k_n} - E(f|D) ∘ T^{s k_n}`
tend to zero in `L²`. -/
theorem wm_main_one (C : CantorData) {s : ℕ} (hs : 1 ≤ s) (D E : Factor S)
    (hDE : D.σ ≤ E.σ)
    (hWM : ∀ g : S.X → ℝ, Measurable[E.σ] g → (∃ K : ℝ, ∀ x, |g x| ≤ K) →
      S.m[g | D.σ] =ᵐ[S.m] 0 → CondWeaklyMixing D g)
    {f : S.X → ℝ} (hfm : Measurable[E.σ] f) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, |f x| ≤ K) :
    Tendsto (fun p : ℕ × ℕ => eLpNorm (fun x => ((p.2 - p.1 : ℕ) : ℝ)⁻¹ *
        ∑ n ∈ Finset.Ico p.1 p.2, (f (S.T^[s * C.enum n] x)
          - (S.m[f | D.σ]) (S.T^[s * C.enum n] x))) 2 S.m) uniformFilter (𝓝 0) := by
  set Ef : S.X → ℝ := S.m[f | D.σ] with hEf_def
  -- a pointwise bounded, `D`-measurable version of `E(f|D)`
  set h : S.X → ℝ := fun y => max (-K) (min K (Ef y)) with hh_def
  have hh_meas : Measurable[D.σ] h :=
    measurable_const.max (measurable_const.min (stronglyMeasurable_condExp (m := D.σ)).measurable)
  have hh_bound : ∀ y, |h y| ≤ K := fun y => by
    rw [abs_le]
    constructor
    · exact le_trans (by linarith) (le_max_left _ _)
    · exact max_le (by linarith) (le_trans (min_le_left _ _) le_rfl)
  have hfint : Integrable f S.m := integrable_of_bdd_const (hfm.mono E.le le_rfl) hK
  have hEf_ae : ∀ᵐ x ∂S.m, |Ef x| ≤ K := abs_condExp_le D hfint hK
  have hh_ae : h =ᵐ[S.m] Ef := hEf_ae.mono fun x hx => by
    have hx' := abs_le.1 hx
    simp only [hh_def]
    rw [min_eq_right hx'.2, max_eq_right hx'.1]
  -- the mean-zero function `g = f - h`
  set g : S.X → ℝ := fun y => f y - h y with hg_def
  have hgE : Measurable[E.σ] g := hfm.sub (hh_meas.mono hDE le_rfl)
  have hgbound : ∀ x, |g x| ≤ K + K := fun x => by
    have := abs_sub (f x) (h x)
    linarith [hK x, hh_bound x]
  have hint_h : Integrable h S.m := integrable_of_bdd_const (hh_meas.mono D.le le_rfl) hh_bound
  -- `E(g|D) = 0`, since `E(h|D) = h` and `h = E(f|D)` almost everywhere
  have hEg : S.m[g | D.σ] =ᵐ[S.m] 0 := by
    have h1 := condExp_sub hfint hint_h D.σ
    have h2 := condExp_of_stronglyMeasurable D.le hh_meas.stronglyMeasurable hint_h
    filter_upwards [h1, hh_ae] with x hx hxh
    change S.m[f - h | D.σ] x = 0
    rw [hx, Pi.sub_apply, h2]
    change Ef x - h x = 0
    linarith [hxh]
  have hcwm := hWM g hgE ⟨K + K, hgbound⟩ hEg
  have hgam : Measurable g := hgE.mono E.le le_rfl
  have hmain := tendsto_avg_of_condWeaklyMixing C hs hgam hgbound hcwm
  refine hmain.congr fun p => ?_
  have hae_all : ∀ᵐ x ∂S.m, ∀ k : ℕ, h (S.T^[k] x) = Ef (S.T^[k] x) := by
    rw [ae_all_iff]
    intro k
    exact (S.measurePreserving_T_iterate k).quasiMeasurePreserving.ae_eq_comp hh_ae
  refine eLpNorm_congr_ae ?_
  filter_upwards [hae_all] with x hx
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [hg_def]
  rw [hx (s * C.enum n)]

end MPS

end CantorSzemeredi

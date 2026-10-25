/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMAverage

/-!
# The `W`-term tends to zero in `L¹`

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`, Step 1, the term
`∫ |avg W_n|` in the per-class bound.  On the probability space `(X, m)` the `L¹` norm is at
most the `L²` norm, so the class averages of the `W_n` tend to zero in `L¹` along the uniform
filter.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Filter Topology

namespace MPS

/-- On a probability space, the integral of the modulus is at most the `L²` norm (when finite). -/
theorem integral_abs_le_eLpNorm_two {S : MPS.{0}} {V : S.X → ℝ}
    (hV : AEStronglyMeasurable V S.m) (hfin : eLpNorm V 2 S.m ≠ ⊤) :
    ∫ x, |V x| ∂S.m ≤ (eLpNorm V 2 S.m).toReal := by
  have h1 : eLpNorm V 1 S.m ≤ eLpNorm V 2 S.m := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have h2 := integral_norm_eq_lintegral_enorm hV
  simp only [Real.norm_eq_abs] at h2
  rw [← eLpNorm_one_eq_lintegral_enorm hV] at h2
  rw [h2]
  exact ENNReal.toReal_mono hfin h1

/-- A family of functions whose `L²` norms tend to zero has integrals of the moduli tending to
zero, along any filter. -/
theorem tendsto_integral_abs_of_eLpNorm {S : MPS.{0}} {ι : Type*} {l : Filter ι}
    {V : ι → S.X → ℝ} (hV : ∀ p, AEStronglyMeasurable (V p) S.m)
    (h : Tendsto (fun p => eLpNorm (V p) 2 S.m) l (𝓝 0)) :
    Tendsto (fun p => ∫ x, |V p x| ∂S.m) l (𝓝 0) := by
  have hT : Tendsto (fun p => (eLpNorm (V p) 2 S.m).toReal) l (𝓝 0) := by
    have := (ENNReal.tendsto_toReal (a := 0) ENNReal.zero_ne_top).comp h
    simpa [Function.comp_def] using this
  have hev : ∀ᶠ p in l, eLpNorm (V p) 2 S.m < 1 := (tendsto_order.1 h).2 1 (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall fun p => integral_nonneg fun x => abs_nonneg _) ?_
  filter_upwards [hev] with p hp
  exact integral_abs_le_eLpNorm_two (hV p) (ne_top_of_lt hp)

/-- The class sums of the blueprint's `W_n` are measurable. -/
theorem measurable_classSum {S : MPS.{0}} (C : CantorData) (s : ℕ → ℕ) (t : ℕ) (D : Factor S)
    (F : ℕ → S.X → ℝ) (hFm : ∀ j, j < t + 1 → Measurable (F j)) (I : Finset ℕ) (K : ℝ) :
    Measurable (fun x => K * ∑ n ∈ I,
      (∏ i ∈ range t, F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum n] x)
        - ∏ i ∈ range t, (S.m[F (i + 1) | D.σ]) (S.T^[(s (i + 1) - s 0) * C.enum n] x))) := by
  refine (measurable_const.mul (Finset.measurable_sum _ fun n _ => ?_))
  refine Measurable.sub ?_ ?_
  · exact Finset.measurable_prod _ fun i hi =>
      (hFm (i + 1) (by have := mem_range.1 hi; omega)).comp (S.measurable_T.iterate _)
  · exact Finset.measurable_prod _ fun i _ => measurable_condExp_iter D (F (i + 1)) _

/-- **The `W`-term tends to zero in `L¹`.**  The `L¹` norms of the class averages of the
blueprint's `W_n` tend to zero along the uniform filter. -/
theorem tendsto_integral_abs_wClass (C : CantorData) (t : ℕ) (hIH : DiffForm C t) (S : MPS.{0})
    (s : ℕ → ℕ) (hs : GoodExp s (t + 1)) (D E : Factor S) (hDE : D.σ ≤ E.σ)
    (hWM : S.WMHyp D E) (ℓ c : ℕ) (hc : c < C.delta ^ ℓ) (F : ℕ → S.X → ℝ) (K : ℝ)
    (hK0 : 0 ≤ K) (hFm : ∀ j, j < t + 1 → Measurable[E.σ] (F j))
    (hFb : ∀ j, j < t + 1 → ∀ x, |F j x| ≤ K) :
    Tendsto (fun p : ℕ × ℕ => ∫ x,
        |(((Ico p.1 p.2).filter (fun n => n % C.delta ^ ℓ = c)).card : ℝ)⁻¹
          * ∑ n ∈ (Ico p.1 p.2).filter (fun n => n % C.delta ^ ℓ = c),
              (∏ i ∈ range t, F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum n] x)
                - ∏ i ∈ range t, (S.m[F (i + 1) | D.σ]) (S.T^[(s (i + 1) - s 0) * C.enum n] x))|
          ∂S.m)
      uniformFilter (𝓝 0) := by
  have hFm' : ∀ j, j < t + 1 → Measurable (F j) := fun j hj => (hFm j hj).mono E.le le_rfl
  refine tendsto_integral_abs_of_eLpNorm (fun p => ?_)
    (tendsto_wClass C t hIH S s hs D E hDE hWM ℓ c hc F K hK0 hFm hFb)
  exact (measurable_classSum C s t D F hFm' _ _).aestronglyMeasurable

end MPS

end CantorSzemeredi

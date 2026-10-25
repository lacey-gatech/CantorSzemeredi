/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMTransfer

/-!
# Pairing with the first factor, and the bound by one conditional expectation

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`, Step 1, "Pairing with `F_1`".
With all factors bounded by `1`, the integral of `F_0 · ∏_{i<t} Exp(F_{i+1}|D)∘T^{e_i k}` equals
the integral of the full product of the `Exp(F_j|D)∘T^{e_j k}`, and the latter is bounded by the
integral of `|Exp(F_{j0}|D)|` for any chosen index `j0`.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Filter Topology

namespace MPS

/-- A bounded measurable function is integrable and lies in `L²`. -/
theorem integrable_memLp_of_bound {S : MPS.{0}} {F : S.X → ℝ} (hm : Measurable F)
    (hb : ∀ x, |F x| ≤ 1) : Integrable F S.m ∧ MemLp F 2 S.m :=
  ⟨integrable_of_bdd_const hm hb,
    MemLp.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hb x)⟩

/-- The conditional expectation of a function bounded by `1` is a.e. bounded by `1`. -/
theorem abs_condExp_ae_le {S : MPS.{0}} (D : Factor S) {F : S.X → ℝ} (hm : Measurable F)
    (hb : ∀ x, |F x| ≤ 1) : ∀ᵐ x ∂S.m, |S.m[F | D.σ] x| ≤ 1 :=
  (condExp_facts D (integrable_memLp_of_bound hm hb).1 hb (integrable_memLp_of_bound hm hb).2 0).1

/-- Integrals are invariant under an iterate of `T`. -/
theorem integral_iterate_comp {S : MPS.{0}} (k : ℕ) (g : S.X → ℝ) :
    ∫ x, g (S.T^[k] x) ∂S.m = ∫ x, g x ∂S.m := by
  have hemb : MeasurableEmbedding S.T^[k] := by
    rw [← S.coe_equivPow k]
    exact (S.equivPow k).measurableEmbedding
  exact (S.measurePreserving_T_iterate k).integral_comp hemb g

/-- The clipped conditional expectation of a function bounded by `1` is a.e. the conditional
expectation, also after pulling back along an iterate of `T`. -/
theorem clip_condExp_ae_iter {S : MPS.{0}} (D : Factor S) {F : S.X → ℝ} (hm : Measurable F)
    (hb : ∀ x, |F x| ≤ 1) (k : ℕ) :
    ∀ᵐ x ∂S.m, max (-1) (min 1 (S.m[F | D.σ] (S.T^[k] x))) = S.m[F | D.σ] (S.T^[k] x) := by
  have h := clip_ae_eq (abs_condExp_ae_le D hm hb)
  exact (S.measurePreserving_T_iterate k).quasiMeasurePreserving.ae h

/-- **Pairing with the first factor.**  The integral of `F_0` times the product of the
conditional expectations of the factors `1, …, t` equals the integral of the full product of
the conditional expectations of all factors, shifted by `T^{(s_j - s_0) k}`. -/
theorem integral_pair_eq (s : ℕ → ℕ) (t : ℕ) (_hs : GoodExp s (t + 1)) {S : MPS.{0}}
    (D : Factor S) (F : ℕ → S.X → ℝ) (hFm : ∀ j, j < t + 1 → Measurable (F j))
    (hFb : ∀ j, j < t + 1 → ∀ x, |F j x| ≤ 1) (k : ℕ) :
    ∫ x, F 0 x * ∏ i ∈ range t, (S.m[F (i + 1) | D.σ]) (S.T^[(s (i + 1) - s 0) * k] x) ∂S.m
      = ∫ x, ∏ j ∈ range (t + 1), (S.m[F j | D.σ]) (S.T^[(s j - s 0) * k] x) ∂S.m := by
  -- the clipped product, which is bounded and `D`-measurable
  set Yc : S.X → ℝ := fun x => ∏ i ∈ range t,
      max (-1) (min 1 (S.m[F (i + 1) | D.σ] (S.T^[(s (i + 1) - s 0) * k] x))) with hYc_def
  have hYc_ae : ∀ᵐ x ∂S.m, Yc x
      = ∏ i ∈ range t, (S.m[F (i + 1) | D.σ]) (S.T^[(s (i + 1) - s 0) * k] x) := by
    have h := (Filter.eventually_all_finset (range t)).2 fun i hi =>
      clip_condExp_ae_iter D (hFm (i + 1) (by have := mem_range.1 hi; omega))
        (hFb (i + 1) (by have := mem_range.1 hi; omega)) ((s (i + 1) - s 0) * k)
    filter_upwards [h] with x hx
    exact Finset.prod_congr rfl fun i hi => hx i hi
  have hYc_meas : Measurable[D.σ] Yc := by
    refine Finset.measurable_prod _ fun i hi => ?_
    have hcl : Measurable[D.σ] (fun y => max (-1) (min 1 (S.m[F (i + 1) | D.σ] y))) :=
      Measurable.max measurable_const (Measurable.min measurable_const
        stronglyMeasurable_condExp.measurable)
    exact measurable_comp_iter D hcl _
  have hYc_bd : ∀ x, |Yc x| ≤ 1 := by
    intro x
    rw [hYc_def]
    simp only
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ =>
      (abs_clip_le zero_le_one _)
  calc ∫ x, F 0 x * ∏ i ∈ range t, (S.m[F (i + 1) | D.σ]) (S.T^[(s (i + 1) - s 0) * k] x) ∂S.m
      = ∫ x, F 0 x * Yc x ∂S.m := by
        refine integral_congr_ae ?_
        filter_upwards [hYc_ae] with x hx
        rw [hx]
    _ = ∫ x, S.m[F 0 | D.σ] x * Yc x ∂S.m :=
        (condExp_facts D (integrable_memLp_of_bound (hFm 0 (by omega)) (hFb 0 (by omega))).1
          (hFb 0 (by omega)) (integrable_memLp_of_bound (hFm 0 (by omega))
            (hFb 0 (by omega))).2 0).2.1 Yc hYc_meas.stronglyMeasurable 1 hYc_bd
    _ = ∫ x, S.m[F 0 | D.σ] x * ∏ i ∈ range t,
          (S.m[F (i + 1) | D.σ]) (S.T^[(s (i + 1) - s 0) * k] x) ∂S.m := by
        refine integral_congr_ae ?_
        filter_upwards [hYc_ae] with x hx
        rw [hx]
    _ = ∫ x, ∏ j ∈ range (t + 1), (S.m[F j | D.σ]) (S.T^[(s j - s 0) * k] x) ∂S.m := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [Finset.prod_range_succ', Nat.sub_self, zero_mul, Function.iterate_zero, id, mul_comm]

/-- **Bound by one conditional expectation.**  The integral of the product of the conditional
expectations of the shifted factors is bounded by the integral of `|Exp(F_{j0}|D)|` for any
index `j0`. -/
theorem abs_integral_prod_le (s : ℕ → ℕ) (t : ℕ) (_hs : GoodExp s (t + 1)) {S : MPS.{0}}
    (D : Factor S) (F : ℕ → S.X → ℝ) (hFm : ∀ j, j < t + 1 → Measurable (F j))
    (hFb : ∀ j, j < t + 1 → ∀ x, |F j x| ≤ 1) (k : ℕ) (j0 : ℕ) (hj0 : j0 < t + 1) :
    |∫ x, ∏ j ∈ range (t + 1), (S.m[F j | D.σ]) (S.T^[(s j - s 0) * k] x) ∂S.m|
      ≤ ∫ x, |S.m[F j0 | D.σ] x| ∂S.m := by
  have hae : ∀ᵐ x ∂S.m, ∀ j ∈ range (t + 1),
      |(S.m[F j | D.σ]) (S.T^[(s j - s 0) * k] x)| ≤ 1 := by
    refine (Filter.eventually_all_finset (range (t + 1))).2 fun j hj => ?_
    have h := abs_condExp_ae_le D (hFm j (mem_range.1 hj)) (hFb j (mem_range.1 hj))
    exact (S.measurePreserving_T_iterate _).quasiMeasurePreserving.ae h
  -- the absolute value of the product is at most the factor at `j0`
  have hpt : ∀ᵐ x ∂S.m, |∏ j ∈ range (t + 1), (S.m[F j | D.σ]) (S.T^[(s j - s 0) * k] x)|
      ≤ |(S.m[F j0 | D.σ]) (S.T^[(s j0 - s 0) * k] x)| := by
    filter_upwards [hae] with x hx
    have hmem : j0 ∈ range (t + 1) := mem_range.2 hj0
    rw [← Finset.mul_prod_erase (range (t + 1)) _ hmem, abs_mul]
    have h1 : |∏ j ∈ (range (t + 1)).erase j0, (S.m[F j | D.σ]) (S.T^[(s j - s 0) * k] x)| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun j hj =>
        hx j (mem_of_mem_erase hj)
    exact mul_le_of_le_one_right (abs_nonneg _) h1
  -- integrability of the bound, and its invariance under the shift
  have hint : Integrable (fun x => |(S.m[F j0 | D.σ]) x|) S.m :=
    (integrable_condExp).abs
  have hint' : Integrable (fun x => |(S.m[F j0 | D.σ]) (S.T^[(s j0 - s 0) * k] x)|) S.m :=
    ((S.measurePreserving_T_iterate _).integrable_comp
      (integrable_condExp).abs.aestronglyMeasurable).2 hint
  calc |∫ x, ∏ j ∈ range (t + 1), (S.m[F j | D.σ]) (S.T^[(s j - s 0) * k] x) ∂S.m|
      ≤ ∫ x, |∏ j ∈ range (t + 1), (S.m[F j | D.σ]) (S.T^[(s j - s 0) * k] x)| ∂S.m :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, |(S.m[F j0 | D.σ]) (S.T^[(s j0 - s 0) * k] x)| ∂S.m :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) hint' hpt
    _ = ∫ x, |(S.m[F j0 | D.σ]) x| ∂S.m := integral_iterate_comp _ (fun y => |(S.m[F j0 | D.σ]) y|)

/-- **Pairing bound.**  The integral of `F_0` times the product of the conditional expectations of
the factors `1, …, t` is bounded, in absolute value, by `∫ |Exp(F_{j0}|D)|` for any index `j0`. -/
theorem abs_integral_pair_le (s : ℕ → ℕ) (t : ℕ) (hs : GoodExp s (t + 1)) {S : MPS.{0}}
    (D : Factor S) (F : ℕ → S.X → ℝ) (hFm : ∀ j, j < t + 1 → Measurable (F j))
    (hFb : ∀ j, j < t + 1 → ∀ x, |F j x| ≤ 1) (k : ℕ) (j0 : ℕ) (hj0 : j0 < t + 1) :
    |∫ x, F 0 x * ∏ i ∈ range t, (S.m[F (i + 1) | D.σ]) (S.T^[(s (i + 1) - s 0) * k] x) ∂S.m|
      ≤ ∫ x, |S.m[F j0 | D.σ] x| ∂S.m := by
  rw [integral_pair_eq s t hs D F hFm hFb k]
  exact abs_integral_prod_le s t hs D F hFm hFb k j0 hj0

end MPS

end CantorSzemeredi

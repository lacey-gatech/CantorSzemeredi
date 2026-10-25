/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMPair

/-!
# Step 1 of `lem:wm-main`: the per-class bound

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`, Step 1, "Pairing with `F_1`"
and "Assembling the classes".  For a finite set `I` of indices and the shifts `k_n`, the average
of the correlations `∫ ∏_{j ≤ t} F_j(T^{(s_j-s_0)k_n} x)` is bounded by the integral of the
absolute value of the averaged difference `W_n = ∏ F_{i+1}∘T^{…} - ∏ Exp(F_{i+1}|D)∘T^{…}`
plus `∫ |Exp(F_{j0}|D)|`.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Filter Topology

namespace MPS

/-- A function that is measurable and a.e. bounded by `C` is integrable. -/
theorem integrable_of_measurable_ae_bound {S : MPS.{0}} {f : S.X → ℝ} (hm : Measurable f)
    {C : ℝ} (hb : ∀ᵐ x ∂S.m, |f x| ≤ C) : Integrable f S.m :=
  (integrable_const C).mono' hm.aestronglyMeasurable
    (hb.mono fun x hx => by rw [Real.norm_eq_abs]; exact hx)

/-- The conditional expectation of a function bounded by `1` is a.e. bounded by `1`, also after
pulling back along an iterate of `T`. -/
theorem abs_condExp_ae_le_iter {S : MPS.{0}} (D : Factor S) {F : S.X → ℝ} (hm : Measurable F)
    (hb : ∀ x, |F x| ≤ 1) (k : ℕ) : ∀ᵐ x ∂S.m, |S.m[F | D.σ] (S.T^[k] x)| ≤ 1 :=
  (S.measurePreserving_T_iterate k).quasiMeasurePreserving.ae (abs_condExp_ae_le D hm hb)

/-- The conditional expectation of a bounded function is measurable (for the ambient σ-algebra),
and remains measurable after composing with an iterate of `T`. -/
theorem measurable_condExp_iter {S : MPS.{0}} (D : Factor S) (F : S.X → ℝ) (k : ℕ) :
    Measurable (fun x => S.m[F | D.σ] (S.T^[k] x)) :=
  ((stronglyMeasurable_condExp (m := D.σ) (μ := S.m) (f := F)).measurable.mono D.le le_rfl).comp
    (S.measurable_T.iterate k)

/-- **Per-class bound (Step 1).**  Let `I` be a finite set of indices, `k : ℕ → ℕ` the shifts,
and `F_j` factors bounded by `1`.  Then the modulus of the average of the correlations
`∫ ∏_{j ≤ t} F_j(T^{(s_j-s_0)k_n} ·)` over `n ∈ I` is at most the integral of the modulus of
the average of `W_n`, plus `∫ |Exp(F_{j0}|D)|`. -/
theorem abs_average_corr_le (s : ℕ → ℕ) (t : ℕ) (hs : GoodExp s (t + 1)) {S : MPS.{0}}
    (D : Factor S) (F : ℕ → S.X → ℝ) (hFm : ∀ j, j < t + 1 → Measurable (F j))
    (hFb : ∀ j, j < t + 1 → ∀ x, |F j x| ≤ 1) (I : Finset ℕ) (kk : ℕ → ℕ) (j0 : ℕ)
    (hj0 : j0 < t + 1) :
    |((I.card : ℝ))⁻¹ * ∑ n ∈ I,
        ∫ x, ∏ j ∈ range (t + 1), F j (S.T^[(s j - s 0) * kk n] x) ∂S.m|
      ≤ ∫ x, |((I.card : ℝ))⁻¹ * ∑ n ∈ I,
          (∏ i ∈ range t, F (i + 1) (S.T^[(s (i + 1) - s 0) * kk n] x)
            - ∏ i ∈ range t, (S.m[F (i + 1) | D.σ]) (S.T^[(s (i + 1) - s 0) * kk n] x))| ∂S.m
        + ∫ x, |S.m[F j0 | D.σ] x| ∂S.m := by
  -- the factors, their products and their differences
  set W : ℕ → S.X → ℝ := fun n x => ∏ i ∈ range t, F (i + 1) (S.T^[(s (i + 1) - s 0) * kk n] x)
    - ∏ i ∈ range t, (S.m[F (i + 1) | D.σ]) (S.T^[(s (i + 1) - s 0) * kk n] x) with hW
  set Y : ℕ → S.X → ℝ := fun n x => ∏ i ∈ range t,
    (S.m[F (i + 1) | D.σ]) (S.T^[(s (i + 1) - s 0) * kk n] x) with hY
  have hF0 : ∀ x, |F 0 x| ≤ 1 := hFb 0 (by omega)
  have hFmeas : ∀ j, j < t + 1 → ∀ n, Measurable (fun x => F j (S.T^[(s j - s 0) * kk n] x)) :=
    fun j hj n => (hFm j hj).comp (S.measurable_T.iterate _)
  -- measurability and bounds of the products
  have hYmeas : ∀ n, Measurable (Y n) := fun n =>
    Finset.measurable_prod _ fun i _ => measurable_condExp_iter D (F (i + 1)) _
  have hYbd : ∀ n, ∀ᵐ x ∂S.m, |Y n x| ≤ 1 := by
    intro n
    have h := (Filter.eventually_all_finset (range t)).2 fun i hi =>
      abs_condExp_ae_le_iter D (hFm (i + 1) (by have := mem_range.1 hi; omega))
        (hFb (i + 1) (by have := mem_range.1 hi; omega)) ((s (i + 1) - s 0) * kk n)
    filter_upwards [h] with x hx
    simp only [hY]
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i hi => hx i hi
  have hPmeas : ∀ n, Measurable (fun x => ∏ i ∈ range t,
      F (i + 1) (S.T^[(s (i + 1) - s 0) * kk n] x)) := fun n =>
    Finset.measurable_prod _ fun i hi => hFmeas (i + 1) (by have := mem_range.1 hi; omega) n
  have hPbd : ∀ n, ∀ x, |∏ i ∈ range t, F (i + 1) (S.T^[(s (i + 1) - s 0) * kk n] x)| ≤ 1 := by
    intro n x
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i hi =>
      hFb (i + 1) (by have := mem_range.1 hi; omega) _
  have hWmeas : ∀ n, Measurable (W n) := fun n => (hPmeas n).sub (hYmeas n)
  have hWbd : ∀ n, ∀ᵐ x ∂S.m, |W n x| ≤ 2 := by
    intro n
    filter_upwards [hYbd n] with x hx
    have h1 := hPbd n x
    have h2 : |W n x| ≤ |∏ i ∈ range t, F (i + 1) (S.T^[(s (i + 1) - s 0) * kk n] x)|
        + |Y n x| := abs_sub _ _
    linarith
  have hWint : ∀ n, Integrable (W n) S.m := fun n =>
    integrable_of_measurable_ae_bound (hWmeas n) (hWbd n)
  have hYint : ∀ n, Integrable (Y n) S.m := fun n =>
    integrable_of_measurable_ae_bound (hYmeas n) (by simpa using hYbd n)
  -- the first factor times a function bounded by `2` is integrable
  have hF0W : ∀ n, Integrable (fun x => F 0 x * W n x) S.m := fun n =>
    integrable_of_measurable_ae_bound (C := 2) ((hFm 0 (by omega)).mul (hWmeas n))
      (hWbd n |>.mono fun x hx => by
        rw [abs_mul]
        nlinarith [hF0 x, hx, abs_nonneg (F 0 x), abs_nonneg (W n x)])
  have hF0Y : ∀ n, Integrable (fun x => F 0 x * Y n x) S.m := fun n =>
    integrable_of_measurable_ae_bound (C := 1) ((hFm 0 (by omega)).mul (hYmeas n))
      (hYbd n |>.mono fun x hx => by
        rw [abs_mul]
        nlinarith [hF0 x, hx, abs_nonneg (F 0 x), abs_nonneg (Y n x)])
  -- the correlation splits into the two pieces
  have hpt : ∀ n x, ∏ j ∈ range (t + 1), F j (S.T^[(s j - s 0) * kk n] x)
      = F 0 x * (W n x + Y n x) := by
    intro n x
    rw [Finset.prod_range_succ']
    simp only [Nat.sub_self, zero_mul, Function.iterate_zero, id_eq, W, Y]
    rw [sub_add_cancel]
    ring
  have hsplit : ∀ n, ∫ x, ∏ j ∈ range (t + 1), F j (S.T^[(s j - s 0) * kk n] x) ∂S.m
      = ∫ x, F 0 x * W n x ∂S.m + ∫ x, F 0 x * Y n x ∂S.m := by
    intro n
    rw [← integral_add (hF0W n) (hF0Y n)]
    congr 1
    funext x
    rw [hpt n x]
    ring
  -- the bound by one conditional expectation, for each index
  have hYbound : ∀ n, |∫ x, F 0 x * Y n x ∂S.m| ≤ ∫ x, |S.m[F j0 | D.σ] x| ∂S.m := fun n =>
    abs_integral_pair_le s t hs D F hFm hFb (kk n) j0 hj0
  have hExp0 : 0 ≤ ∫ x, |S.m[F j0 | D.σ] x| ∂S.m := integral_nonneg fun _ => abs_nonneg _
  by_cases hI : I.card = 0
  · rw [Finset.card_eq_zero.1 hI]
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, inv_zero, zero_mul,
      mul_zero, abs_zero, integral_zero]
    linarith
  have hK : (0 : ℝ) < (I.card : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hI)
  have hSWint : Integrable (fun x => ∑ n ∈ I, W n x) S.m :=
    integrable_finsetSum I fun n _ => hWint n
  -- the first pieces add up to one integral of `F_0 · ∑ W_n`
  have hA : ∫ x, F 0 x * ∑ n ∈ I, W n x ∂S.m = ∑ n ∈ I, ∫ x, F 0 x * W n x ∂S.m := by
    rw [← integral_finset_sum I fun n _ => hF0W n]
    congr 1
    funext x
    rw [Finset.mul_sum]
  have hAbound : |∫ x, F 0 x * ∑ n ∈ I, W n x ∂S.m| ≤ ∫ x, |∑ n ∈ I, W n x| ∂S.m := by
    refine le_trans abs_integral_le_integral_abs ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
      hSWint.abs (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hF0 x)
  have hB : |∑ n ∈ I, ∫ x, F 0 x * Y n x ∂S.m|
      ≤ (I.card : ℝ) * ∫ x, |S.m[F j0 | D.σ] x| ∂S.m := by
    calc |∑ n ∈ I, ∫ x, F 0 x * Y n x ∂S.m|
        ≤ ∑ n ∈ I, |∫ x, F 0 x * Y n x ∂S.m| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ I, ∫ x, |S.m[F j0 | D.σ] x| ∂S.m := Finset.sum_le_sum fun n _ => hYbound n
      _ = (I.card : ℝ) * ∫ x, |S.m[F j0 | D.σ] x| ∂S.m := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hR : ∫ x, |((I.card : ℝ))⁻¹ * ∑ n ∈ I, W n x| ∂S.m
      = ((I.card : ℝ))⁻¹ * ∫ x, |∑ n ∈ I, W n x| ∂S.m := by
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [abs_mul, abs_of_pos (inv_pos.2 hK)]
  rw [Finset.sum_congr rfl fun n _ => hsplit n, Finset.sum_add_distrib, ← hA, hR]
  have h1 := abs_add_le (∫ x, F 0 x * ∑ n ∈ I, W n x ∂S.m)
    (∑ n ∈ I, ∫ x, F 0 x * Y n x ∂S.m)
  have h2 : ((I.card : ℝ))⁻¹ * |∫ x, F 0 x * ∑ n ∈ I, W n x ∂S.m
      + ∑ n ∈ I, ∫ x, F 0 x * Y n x ∂S.m|
      ≤ ((I.card : ℝ))⁻¹ * (∫ x, |∑ n ∈ I, W n x| ∂S.m
        + (I.card : ℝ) * ∫ x, |S.m[F j0 | D.σ] x| ∂S.m) :=
    mul_le_mul_of_nonneg_left (le_trans h1 (add_le_add hAbound hB)) (inv_nonneg.2 hK.le)
  rw [abs_mul, abs_of_pos (inv_pos.2 hK)]
  calc ((I.card : ℝ))⁻¹ * |∫ x, F 0 x * ∑ n ∈ I, W n x ∂S.m
        + ∑ n ∈ I, ∫ x, F 0 x * Y n x ∂S.m|
      ≤ ((I.card : ℝ))⁻¹ * (∫ x, |∑ n ∈ I, W n x| ∂S.m
        + (I.card : ℝ) * ∫ x, |S.m[F j0 | D.σ] x| ∂S.m) := h2
    _ = ((I.card : ℝ))⁻¹ * ∫ x, |∑ n ∈ I, W n x| ∂S.m
        + ∫ x, |S.m[F j0 | D.σ] x| ∂S.m := by
          rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul]

end MPS

end CantorSzemeredi

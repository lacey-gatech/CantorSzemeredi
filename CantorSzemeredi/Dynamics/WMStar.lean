/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMVdC
import CantorSzemeredi.Dynamics.WMAverageShift

/-!
# Step 3 of `lem:wm-main`: the conclusion, and the induction on the number of factors

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`, Step 3.  The van der Corput
inequality, applied to the products `u_n` on a window, together with the averaged shift estimate,
gives `‖avg u_n‖₂² ≤ 20 √ε` for long windows.  This is the statement `P(t+1)` from `P(t)`, which
closes the induction.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Filter Topology

namespace MPS

/-- Sums over `Icc 1 H` are sums over the shifts `h + 1`, `h < H`. -/
theorem sum_Icc_one_eq_range (F : ℕ → ℝ) (H : ℕ) :
    ∑ h ∈ Icc 1 H, F h = ∑ h ∈ range H, F (h + 1) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ H + 1), ih, Finset.sum_range_succ]

/-- **The window estimate (Step 3).**  For `ε ∈ (0,1]`, there is a threshold `L` such that the mean
square of the window averages of `u_n` over windows `[M,N)` with `N − M ≥ L` is at most `20 √ε`. -/
theorem window_mean_sq_le {t : ℕ} (C : CantorData) (hIH : DiffForm C t) {S : MPS.{0}}
    [StandardBorelSpace S.X] (D E : Factor S) (hDE : D.σ ≤ E.σ) (hWM : S.WMHyp D E)
    (s : ℕ → ℕ) (hs : GoodExp s (t + 1)) (f : ℕ → S.X → ℝ)
    (hfE : ∀ j, j < t + 1 → Measurable[E.σ] (f j))
    (hfb : ∀ j, j < t + 1 → ∀ x, |f j x| ≤ 1) (j0 : ℕ) (hj0 : j0 < t + 1)
    (hmean : S.m[f j0 | D.σ] =ᵐ[S.m] 0) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ L : ℕ, ∀ M N : ℕ, L ≤ N - M →
      ∫ x, ((((N - M : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico M N,
          ∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x)) ^ 2 ∂S.m ≤ 20 * Real.sqrt ε := by
  set u : ℕ → S.X → ℝ := fun n x => ∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x) with hu
  have hum : ∀ n, Measurable (u n) := fun n =>
    Finset.measurable_prod _ fun j hj =>
      ((hfE j (Finset.mem_range.1 hj)).mono E.le le_rfl).comp (S.measurable_T.iterate _)
  have hub : ∀ n x, |u n x| ≤ 1 := fun n x =>
    abs_prod_le_one_of _ _ fun j hj => hfb j (Finset.mem_range.1 hj) _
  obtain ⟨H, hH, hHε, hLH⟩ := shift_average_bound C t hIH D E hDE hWM s hs f hfE hfb j0 hj0
    hmean ε hε0 hε1
  -- a shift scale `ℓ` with `H < ε δ^ℓ`
  have hδ : (1 : ℝ) < (C.delta : ℝ) := by
    have := C.two_le_delta
    exact_mod_cast (by omega : 1 < C.delta)
  obtain ⟨ℓ, hℓ⟩ := pow_unbounded_of_one_lt ((H : ℝ) / ε) hδ
  have hℓ' : (H : ℝ) < ε * ((C.delta ^ ℓ : ℕ) : ℝ) := by
    push_cast
    rw [div_lt_iff₀ hε0] at hℓ
    linarith
  obtain ⟨L, hL⟩ := hLH ℓ hℓ'
  refine ⟨L + H + 1, fun M N hLN => ?_⟩
  have hHL : H < N - M := by omega
  have hv := vdc_products u hum hub M N H hH hHL
  -- the shifted sums of `vdc_products` are the shift averages
  have hsum : ∑ h ∈ Icc 1 H, |∑ n ∈ Ico M (N - h), ∫ x, u (n + h) x * u n x ∂S.m|
        / ((N - M - h : ℕ) : ℝ)
      = ∑ h ∈ range H, |((N - (h + 1) - M : ℕ) : ℝ)⁻¹ * ∑ n ∈ Ico M (N - (h + 1)),
          ∫ x, u (n + (h + 1)) x * u n x ∂S.m| := by
    rw [sum_Icc_one_eq_range (fun h => |∑ n ∈ Ico M (N - h), ∫ x, u (n + h) x * u n x ∂S.m|
        / ((N - M - h : ℕ) : ℝ)) H]
    refine Finset.sum_congr rfl fun h hh => ?_
    have hh' : h + 1 ≤ H := by
      have := Finset.mem_range.1 hh
      omega
    have hden : N - (h + 1) - M = N - M - (h + 1) := by omega
    have hc0 : (0 : ℝ) ≤ ((N - M - (h + 1) : ℕ) : ℝ)⁻¹ := by positivity
    rw [hden, abs_mul, abs_of_nonneg hc0, div_eq_inv_mul]
  have hmain : (H : ℝ)⁻¹ * ∑ h ∈ range H, |((N - (h + 1) - M : ℕ) : ℝ)⁻¹
      * ∑ n ∈ Ico M (N - (h + 1)), ∫ x, u (n + (h + 1)) x * u n x ∂S.m| ≤ 3 * ε + Real.sqrt (2 * ε) :=
    hL M N (by omega)
  rw [hsum] at hv
  -- the arithmetic of the constants
  have hsq : Real.sqrt (2 * ε) ≤ 3 / 2 * Real.sqrt ε := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hε0.le]
  have hεr : ε ≤ Real.sqrt ε := by
    have h1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.2 hε1
    have h2 := Real.sq_sqrt hε0.le
    nlinarith [Real.sqrt_nonneg ε]
  have hH2 : 2 / (H : ℝ) ≤ 2 * ε := by
    have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
    rw [div_le_iff₀ hHpos]
    rw [div_le_iff₀ hε0] at hHε
    nlinarith
  calc _ ≤ 4 * ((H : ℝ)⁻¹ * ∑ h ∈ range H, |((N - (h + 1) - M : ℕ) : ℝ)⁻¹
      * ∑ n ∈ Ico M (N - (h + 1)), ∫ x, u (n + (h + 1)) x * u n x ∂S.m|) + 2 / (H : ℝ) := hv
    _ ≤ 20 * Real.sqrt ε := by linarith

/-- The window averages of the products, as bounded measurable functions. -/
theorem memLp_avg_window {t : ℕ} {S : MPS.{0}} (s : ℕ → ℕ) (C : CantorData) (E : Factor S)
    (f : ℕ → S.X → ℝ) (hfE : ∀ j, j < t + 1 → Measurable[E.σ] (f j))
    (hfb : ∀ j, j < t + 1 → ∀ x, |f j x| ≤ 1) (M N : ℕ) :
    MemLp (fun x => ((((N - M : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico M N,
      ∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x))) 2 S.m := by
  have hum : ∀ n, Measurable (fun x => ∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x)) :=
    fun n => Finset.measurable_prod _ fun j hj =>
      ((hfE j (Finset.mem_range.1 hj)).mono E.le le_rfl).comp (S.measurable_T.iterate _)
  have hm : Measurable (fun x => ((((N - M : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico M N,
      ∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x))) :=
    measurable_const.mul (Finset.measurable_sum _ fun n _ => hum n)
  have hbd : ∀ x, |((((N - M : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico M N,
      ∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x))| ≤ 1 := by
    intro x
    rcases Nat.eq_zero_or_pos (N - M) with h0 | hpos
    · simp [h0]
    have hposR : (0 : ℝ) < ((N - M : ℕ) : ℝ) := by exact_mod_cast hpos
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hposR.le)]
    have hsum : |∑ n ∈ Ico M N, ∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x)|
        ≤ ((N - M : ℕ) : ℝ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ n ∈ Ico M N, |∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x)|
          ≤ ∑ n ∈ Ico M N, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => abs_prod_le_one_of _ _ fun j hj =>
              hfb j (Finset.mem_range.1 hj) _
        _ = ((N - M : ℕ) : ℝ) := by simp
    calc ((N - M : ℕ) : ℝ)⁻¹ * |∑ n ∈ Ico M N, ∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x)|
        ≤ ((N - M : ℕ) : ℝ)⁻¹ * ((N - M : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hposR.le)
      _ = 1 := inv_mul_cancel₀ hposR.ne'
  exact MemLp.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hbd x)

/-- **Step 3: the star form for `t + 1`.**  The induction hypothesis `DiffForm C t` gives the
window estimate, the mean squares of the averages tend to zero along the uniform filter, hence the
`L²` norms of the averages do. -/
theorem star_step {t : ℕ} (C : CantorData) (hIH : DiffForm C t) : StarForm C (t + 1) := by
  intro S _ D E hDE hWM s hs f hfE hfb j0 hj0 hmean
  have hsq : Tendsto (fun p : ℕ × ℕ => ∫ x, (avgProd C s (t + 1) f p x) ^ 2 ∂S.m)
      uniformFilter (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    set ε : ℝ := min 1 ((δ / 40) ^ 2) with hεdef
    have hε0 : 0 < ε := lt_min one_pos (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hsqrt : Real.sqrt ε ≤ δ / 40 := by
      rw [Real.sqrt_le_left (by positivity)]
      exact min_le_right _ _
    obtain ⟨L, hL⟩ := window_mean_sq_le C hIH D E hDE hWM s hs f hfE hfb j0 hj0 hmean ε hε0 hε1
    have hset : {p : ℕ × ℕ | L ≤ p.2 - p.1} ∈ uniformFilter :=
      mem_uniformFilter_iff.2 ⟨L, fun M N h => h⟩
    refine Filter.eventually_of_mem hset fun p hp => ?_
    have hbound : ∫ x, (avgProd C s (t + 1) f p x) ^ 2 ∂S.m ≤ 20 * Real.sqrt ε :=
      hL p.1 p.2 hp
    have hnn : 0 ≤ ∫ x, (avgProd C s (t + 1) f p x) ^ 2 ∂S.m :=
      integral_nonneg fun x => sq_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith
  have hfin : ∀ p : ℕ × ℕ, MemLp (avgProd C s (t + 1) f p) 2 S.m := fun p =>
    memLp_avg_window s C E f hfE hfb p.1 p.2
  refine (ENNReal.tendsto_toReal_iff (fun p => (hfin p).eLpNorm_ne_top) ENNReal.zero_ne_top).1 ?_
  rw [ENNReal.toReal_zero]
  have hreal : ∀ p : ℕ × ℕ, (eLpNorm (avgProd C s (t + 1) f p) 2 S.m).toReal
      = Real.sqrt (∫ x, (avgProd C s (t + 1) f p x) ^ 2 ∂S.m) := fun p => by
    rw [integral_sq_eq_eLpNorm_sq (hfin p), Real.sqrt_sq ENNReal.toReal_nonneg]
  rw [show (fun p : ℕ × ℕ => (eLpNorm (avgProd C s (t + 1) f p) 2 S.m).toReal)
      = fun p => Real.sqrt (∫ x, (avgProd C s (t + 1) f p x) ^ 2 ∂S.m) from funext hreal]
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at this
  exact this

/-- The star form holds for every number of factors, by induction. -/
theorem starForm_all (C : CantorData) : ∀ t, StarForm C t := by
  intro t
  induction t with
  | zero =>
    intro S _ D E _ _ s _ f _ _ j0 hj0 _
    exact absurd hj0 (Nat.not_lt_zero _)
  | succ t ih => exact star_step C (diff_of_star C t ih)

end MPS

end CantorSzemeredi

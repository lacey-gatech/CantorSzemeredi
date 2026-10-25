/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.VanDerCorput
import CantorSzemeredi.Dynamics.WMAverageShift

/-!
# The van der Corput inequality for products on a window

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`, Step 3.  For bounded functions
`g_n` (indexed by `n ∈ ℕ`) and a window `[M, N)`, the mean square of the window average is bounded
by the correlations `∫ g_{n+h} g_n` over the shortened windows `[M, N−h)`, `1 ≤ h ≤ H`, by applying
the van der Corput inequality in `L²` after extending the functions by zero outside the window.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Filter Topology

/-- The `ℤ`-interval sum equals the `ℕ`-interval sum, for a nonnegative window. -/
theorem sum_Ico_natCast_int (F : ℤ → ℝ) (a b : ℕ) :
    ∑ k ∈ Ico (a : ℤ) b, F k = ∑ n ∈ Ico a b, F n := by
  refine Finset.sum_nbij' (fun k => k.toNat) (fun n => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Ico] at hk ⊢
    omega
  · intro n hn
    rw [Finset.mem_Ico] at hn ⊢
    omega
  · intro k hk
    rw [Finset.mem_Ico] at hk
    omega
  · intro n _
    simp
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Int.toNat_of_nonneg (by omega)]

/-- The `ℤ`-interval sum over `Icc 1 H` equals the `ℕ` one. -/
theorem sum_Icc_natCast_int (F : ℤ → ℝ) (H : ℕ) :
    ∑ h ∈ Icc (1 : ℤ) H, F h = ∑ h ∈ Icc 1 H, F h := by
  refine Finset.sum_nbij' (fun k => k.toNat) (fun n => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    omega
  · intro n _
    simp
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Int.toNat_of_nonneg (by omega)]

/-- Finite sums of `L²` classes are the `L²` class of the pointwise sum (real version). -/
theorem coeFn_finset_sum_lpR {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    (s : Finset ι) (F : ι → Lp ℝ 2 μ) :
    (∑ i ∈ s, F i : Lp ℝ 2 μ) =ᵐ[μ] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ 2 μ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

namespace MPS

/-- **The van der Corput inequality for products on a window.**  For bounded measurable functions
`g n` with `|g n| ≤ 1`, the mean square of the window average over `[M, N)` is at most
`4 H⁻¹ Σ_{1 ≤ h ≤ H} |∫-correlation over [M, N−h)| / (N−M−h) + 2/H`. -/
theorem vdc_products {S : MPS.{0}} (g : ℕ → S.X → ℝ) (hg : ∀ n, Measurable (g n))
    (hb : ∀ n x, |g n x| ≤ 1) (M N H : ℕ) (hH : 1 ≤ H) (hHL : H < N - M) :
    ∫ x, ((((N - M : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico M N, g n x) ^ 2 ∂S.m
      ≤ 4 * ((H : ℝ)⁻¹ * ∑ h ∈ Icc 1 H,
          |∑ n ∈ Ico M (N - h), ∫ x, g (n + h) x * g n x ∂S.m| / ((N - M - h : ℕ) : ℝ))
        + 2 / (H : ℝ) := by
  -- the zero extension of the functions outside the window
  set G : ℤ → S.X → ℝ := fun k x => if (M : ℤ) ≤ k ∧ k < (N : ℤ) then g k.toNat x else 0 with hG
  have hGm : ∀ k, Measurable (G k) := fun k => by
    simp only [hG]
    split_ifs
    · exact hg _
    · exact measurable_const
  have hGb : ∀ k x, |G k x| ≤ 1 := fun k x => by
    simp only [hG]
    split_ifs
    · exact hb _ _
    · simp
  have hGmem : ∀ k, MemLp (G k) 2 S.m := fun k =>
    MemLp.of_bound (hGm k).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hGb k x)
  set w : ℤ → Lp ℝ 2 S.m := fun k => (hGmem k).toLp (G k) with hw
  have hu : ((measureUnivNNReal S.m : NNReal) : ℝ) = 1 := by
    simp [measureUnivNNReal]
  have hwnorm : ∀ k, ‖w k‖ ≤ 1 := fun k => by
    have := Lp.norm_le_of_ae_bound (μ := S.m) (f := w k) zero_le_one
      ((hw ▸ (hGmem k).coeFn_toLp : ∀ᵐ x ∂S.m, w k x = G k x).mono fun x hx => by
        rw [hx, Real.norm_eq_abs]
        exact hGb k x)
    rw [hu] at this
    simpa using this
  have hwz : ∀ k, k ∉ Ico (M : ℤ) N → w k = 0 := fun k hk => by
    apply Lp.ext
    filter_upwards [(hGmem k).coeFn_toLp, Lp.coeFn_zero ℝ 2 S.m] with x h1 h2
    rw [hw]
    simp only
    rw [h1, h2]
    have : ¬ ((M : ℤ) ≤ k ∧ k < (N : ℤ)) := fun h => hk (Finset.mem_Ico.2 h)
    simp [hG, this]
  have hVdC : VdCData w (M : ℤ) (N : ℤ) := ⟨hwnorm, hwz⟩
  have key := hVdC.van_der_corput_avg (H := (H : ℤ)) (by exact_mod_cast hH) (by omega)
  -- the window average, as a function and as an `L²` class
  have hNMpos : 0 < N - M := by omega
  set F : S.X → ℝ := fun x => (((N - M : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico M N, g n x with hF
  have hFm : Measurable F := measurable_const.mul (Finset.measurable_sum _ fun n _ => hg n)
  have hFb : ∀ x, |F x| ≤ 1 := fun x => by
    rw [hF]
    simp only
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
    have hsum : |∑ n ∈ Ico M N, g n x| ≤ ((N - M : ℕ) : ℝ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ n ∈ Ico M N, |g n x| ≤ ∑ n ∈ Ico M N, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => hb n x
        _ = ((N - M : ℕ) : ℝ) := by simp
    have hpos : (0 : ℝ) < ((N - M : ℕ) : ℝ) := by exact_mod_cast hNMpos
    calc ((N - M : ℕ) : ℝ)⁻¹ * |∑ n ∈ Ico M N, g n x| ≤ ((N - M : ℕ) : ℝ)⁻¹ * ((N - M : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hpos.le)
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  have hFmem : MemLp F 2 S.m :=
    MemLp.of_bound hFm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hFb x)
  have hcast : (((N : ℤ) - (M : ℤ) : ℤ) : ℝ) = ((N - M : ℕ) : ℝ) := by
    rw [show (N : ℤ) - (M : ℤ) = ((N - M : ℕ) : ℤ) by omega]
    exact Int.cast_natCast _
  have hae : ∀ᵐ x ∂S.m, ∀ k ∈ Ico (M : ℤ) N, w k x = G k x :=
    (Filter.eventually_all_finset _).2 fun k _ => (hGmem k).coeFn_toLp
  have hsum_eq : (((N : ℤ) - (M : ℤ) : ℤ) : ℝ)⁻¹ • ∑ n ∈ Ico (M : ℤ) N, w n = hFmem.toLp F := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (((N : ℤ) - (M : ℤ) : ℤ) : ℝ)⁻¹
        (∑ n ∈ Ico (M : ℤ) N, w n), coeFn_finset_sum_lpR (Ico (M : ℤ) N) w,
        hFmem.coeFn_toLp, hae] with x h1 h2 h3 h4
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    rw [h1, h2, h3]
    rw [Finset.sum_congr rfl fun k hk => h4 k hk]
    rw [sum_Ico_natCast_int (fun k => G k x) M N]
    rw [hF]
    simp only
    rw [hcast]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_Ico.1 hn
    simp only [hG]
    rw [if_pos ⟨by omega, by omega⟩, Int.toNat_natCast]
  have hL : ‖(((N : ℤ) - (M : ℤ) : ℤ) : ℝ)⁻¹ • ∑ n ∈ Ico (M : ℤ) N, w n‖ ^ 2
      = ∫ x, F x ^ 2 ∂S.m := by
    rw [hsum_eq]
    have hnorm : ‖hFmem.toLp F‖ = (eLpNorm F 2 S.m).toReal := by
      rw [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_ae hFmem.coeFn_toLp
    rw [hnorm, integral_sq_eq_eLpNorm_sq hFmem]
  -- the inner products are integrals of the zero extensions
  have hinner : ∀ a b : ℤ, inner ℝ (w a) (w b) = ∫ x, G a x * G b x ∂S.m := by
    intro a b
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hGmem a).coeFn_toLp, (hGmem b).coeFn_toLp] with x h1 h2
    simp only [w]
    rw [h1, h2]
    simp [mul_comm]
  -- the correlations are the sums over the shortened windows
  have hcorr : ∀ h : ℕ, h ≤ N - M →
      corr w (M : ℤ) (N : ℤ) (h : ℤ) = ∑ n ∈ Ico M (N - h), ∫ x, g (n + h) x * g n x ∂S.m := by
    intro h hh
    unfold corr
    simp only [hinner]
    rw [sum_Ico_natCast_int (fun k => ∫ x, G (k + (h : ℤ)) x * G k x ∂S.m) M N]
    have hsub : Ico M (N - h) ⊆ Ico M N := Finset.Ico_subset_Ico_right (Nat.sub_le _ _)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hn' := Finset.mem_Ico.1 hn
      congr 1
      funext x
      simp only [hG]
      rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩]
      congr 2 <;> omega
    · intro n hn hn'
      have hn1 := Finset.mem_Ico.1 hn
      have hn2 : ¬ (n < N - h) := fun h' => hn' (Finset.mem_Ico.2 ⟨hn1.1, h'⟩)
      have hzero : ∀ x, G ((n : ℤ) + (h : ℤ)) x = 0 := fun x => by
        simp only [hG]
        rw [if_neg (fun h' => by omega)]
      simp [hzero]
  -- the shifted sums, from `ℤ` to `ℕ`
  have hdenom : ∀ h : ℕ, h ≤ N - M →
      ((((N : ℤ) - (M : ℤ) - (h : ℤ)) : ℤ) : ℝ) = ((N - M - h : ℕ) : ℝ) := by
    intro h hh
    rw [show (N : ℤ) - (M : ℤ) - (h : ℤ) = ((N - M - h : ℕ) : ℤ) by omega]
    exact Int.cast_natCast _
  have hsumeq : ∑ h ∈ Icc (1 : ℤ) (H : ℤ),
      |corr w (M : ℤ) (N : ℤ) h| / ((((N : ℤ) - (M : ℤ) - h) : ℤ) : ℝ)
      = ∑ h ∈ Icc 1 H, |∑ n ∈ Ico M (N - h), ∫ x, g (n + h) x * g n x ∂S.m|
          / ((N - M - h : ℕ) : ℝ) := by
    rw [sum_Icc_natCast_int (fun h : ℤ => |corr w (M : ℤ) (N : ℤ) h|
      / ((((N : ℤ) - (M : ℤ) - h) : ℤ) : ℝ))]
    refine Finset.sum_congr rfl fun h hh => ?_
    have hh' := Finset.mem_Icc.1 hh
    have hle : h ≤ N - M := by omega
    rw [hcorr h hle, hdenom h hle]
  have hkey := hVdC.van_der_corput_avg (H := (H : ℤ)) (by exact_mod_cast hH) (by omega)
  rw [hL, hsumeq] at hkey
  push_cast at hkey
  exact hkey

end MPS

end CantorSzemeredi

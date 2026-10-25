/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMSpectral

/-!
# Averaging over the shifts: the Cauchy–Schwarz step

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`, Step 2, "From `φ` to `ψ`".
The averages over the shifted windows `[M, N_h)` of `φ` are controlled, after averaging over the
shifts `h`, by the square root of the averages of `ψ`, using `φ² ≤ ψ` and Cauchy–Schwarz.
-/

namespace CantorSzemeredi

open Finset

/-- **Cauchy–Schwarz for the shift average.**  If `φ² ≤ ψ` and the windows `[M, N_h)` are at least
half of `[M, N)`, then the square of the average over `h < H` of the window averages of `φ` is at
most `2/(H (N-M))` times the sum of `ψ` over all `h < H` and `n ∈ [M, N)`. -/
theorem cs_avg_bound (H M N : ℕ) (hH : 0 < H) (hN : 0 < N - M) (Nh : ℕ → ℕ)
    (hNhN : ∀ h ∈ range H, Nh h ≤ N) (hNhM : ∀ h ∈ range H, M ≤ Nh h)
    (hL : ∀ h ∈ range H, N - M ≤ 2 * (Nh h - M))
    (φ ψ : ℕ → ℕ → ℝ) (hφ0 : ∀ h n, 0 ≤ φ h n) (hψ0 : ∀ h n, 0 ≤ ψ h n)
    (hpsi : ∀ h n, φ h n ^ 2 ≤ ψ h n) :
    ((H : ℝ)⁻¹ * ∑ h ∈ range H,
        (((Nh h - M : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico M (Nh h), φ h n) ^ 2
      ≤ (2 / ((H : ℝ) * ((N - M : ℕ) : ℝ))) * ∑ h ∈ range H, ∑ n ∈ Ico M N, ψ h n := by
  -- the window of `h` has at least half the length of `[M, N)`
  have hLpos : ∀ h ∈ range H, 0 < Nh h - M := fun h hh => by
    have := hL h hh
    omega
  have hLr : ∀ h ∈ range H, (0 : ℝ) < ((Nh h - M : ℕ) : ℝ) := fun h hh => by
    exact_mod_cast hLpos h hh
  have hNMr : (0 : ℝ) < ((N - M : ℕ) : ℝ) := by exact_mod_cast hN
  -- the square of each window average is at most the window average of `ψ` on `[M, N)`
  have hsq : ∀ h ∈ range H, ((((Nh h - M : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico M (Nh h), φ h n) ^ 2
      ≤ (2 / ((N - M : ℕ) : ℝ)) * ∑ n ∈ Ico M N, ψ h n := by
    intro h hh
    set L : ℝ := ((Nh h - M : ℕ) : ℝ) with hLdef
    have hcard : (((Ico M (Nh h)).card : ℕ) : ℝ) = L := by
      rw [Nat.card_Ico, hLdef]
    have hcs := sq_sum_le_card_mul_sum_sq (s := Ico M (Nh h)) (f := fun n => φ h n)
    have hcs' : (∑ n ∈ Ico M (Nh h), φ h n) ^ 2 ≤ L * ∑ n ∈ Ico M (Nh h), φ h n ^ 2 := by
      have := hcs
      rw [← hcard]
      exact_mod_cast this
    have hψsub : ∑ n ∈ Ico M (Nh h), ψ h n ≤ ∑ n ∈ Ico M N, ψ h n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (hNhN h hh))
        fun n _ _ => hψ0 h n
    have hφψ' : ∑ n ∈ Ico M (Nh h), φ h n ^ 2 ≤ ∑ n ∈ Ico M N, ψ h n := by
      refine le_trans (Finset.sum_le_sum fun n _ => hpsi h n) ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (hNhN h hh))
        fun n _ _ => hψ0 h n
    have hinv : L⁻¹ ≤ 2 / ((N - M : ℕ) : ℝ) := by
      rw [inv_eq_one_div, div_le_div_iff₀ (hLr h hh) hNMr]
      have : ((N - M : ℕ) : ℝ) ≤ 2 * L := by
        rw [hLdef]
        exact_mod_cast hL h hh
      linarith
    have hX : 0 ≤ ∑ n ∈ Ico M N, ψ h n := Finset.sum_nonneg fun n _ => hψ0 h n
    calc ((L)⁻¹ * ∑ n ∈ Ico M (Nh h), φ h n) ^ 2
        = (L⁻¹) ^ 2 * (∑ n ∈ Ico M (Nh h), φ h n) ^ 2 := by ring
      _ ≤ (L⁻¹) ^ 2 * (L * ∑ n ∈ Ico M (Nh h), φ h n ^ 2) :=
          mul_le_mul_of_nonneg_left hcs' (sq_nonneg _)
      _ = L⁻¹ * ∑ n ∈ Ico M (Nh h), φ h n ^ 2 := by
          field_simp
      _ ≤ (2 / ((N - M : ℕ) : ℝ)) * ∑ n ∈ Ico M N, ψ h n := by
          refine le_trans (mul_le_mul_of_nonneg_right hinv ?_) ?_
          · exact Finset.sum_nonneg fun n _ => sq_nonneg _
          · exact mul_le_mul_of_nonneg_left hφψ' (by positivity)
  -- Cauchy–Schwarz over the shifts
  set Tv : ℕ → ℝ := fun h => (((Nh h - M : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico M (Nh h), φ h n with hTv
  have hCS : (∑ h ∈ range H, Tv h) ^ 2 ≤ (H : ℝ) * ∑ h ∈ range H, Tv h ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range H) (f := Tv)
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hsum : ∑ h ∈ range H, Tv h ^ 2
      ≤ (2 / ((N - M : ℕ) : ℝ)) * ∑ h ∈ range H, ∑ n ∈ Ico M N, ψ h n := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun h hh => hsq h hh
  have hHr : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  calc ((H : ℝ)⁻¹ * ∑ h ∈ range H, Tv h) ^ 2
      = ((H : ℝ)⁻¹) ^ 2 * (∑ h ∈ range H, Tv h) ^ 2 := by ring
    _ ≤ ((H : ℝ)⁻¹) ^ 2 * ((H : ℝ) * ∑ h ∈ range H, Tv h ^ 2) :=
        mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ ≤ ((H : ℝ)⁻¹) ^ 2 * ((H : ℝ) * ((2 / ((N - M : ℕ) : ℝ)) *
          ∑ h ∈ range H, ∑ n ∈ Ico M N, ψ h n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hHr.le) (sq_nonneg _)
    _ = (2 / ((H : ℝ) * ((N - M : ℕ) : ℝ))) * ∑ h ∈ range H, ∑ n ∈ Ico M N, ψ h n := by
        field_simp

namespace MPS

open MeasureTheory

/-- **`φ² ≤ ψ`.**  The square of the integral of `|⟨T^v f, f⟩_D|` is at most the integral of
`⟨T^v f, f⟩_D²`, since the variance is nonnegative on the probability space `(X, m)`. -/
theorem phiCorr_sq_le_psi {S : MPS.{0}} (D : Factor S) {f : S.X → ℝ} (hm : Measurable f)
    (hb : ∀ x, |f x| ≤ 1) (v : ℕ) :
    (phiCorr S D f v) ^ 2 ≤ ∫ x, (condInner D (f ∘ S.T^[v]) f x) ^ 2 ∂S.m := by
  set c : S.X → ℝ := condInner D (f ∘ S.T^[v]) f with hc
  set m : ℝ := ∫ x, |c x| ∂S.m with hm_def
  have hcm : Measurable c := by
    have h1 : Measurable (S.m[(f ∘ S.T^[v]) * f | D.σ]) :=
      (stronglyMeasurable_condExp.measurable).mono D.le le_rfl
    exact h1
  have hcb : ∀ᵐ x ∂S.m, |c x| ≤ 1 := by
    have hmeas : Measurable ((f ∘ S.T^[v]) * f) :=
      ((hm.comp (S.measurable_T.iterate v))).mul hm
    have hbd : ∀ x, |((f ∘ S.T^[v]) * f) x| ≤ 1 := fun x => by
      simp only [Pi.mul_apply, Function.comp_apply]
      rw [abs_mul]
      exact mul_le_one₀ (hb _) (abs_nonneg _) (hb _)
    exact abs_condExp_ae_le D hmeas hbd
  have hint1 : Integrable (fun x => |c x|) S.m :=
    integrable_of_measurable_ae_bound hcm.abs (C := 1) (hcb.mono fun x hx => by
      rw [abs_abs]; exact hx)
  have hint2 : Integrable (fun x => c x ^ 2) S.m :=
    integrable_of_measurable_ae_bound (hcm.pow_const 2) (C := 1) (hcb.mono fun x hx => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (c x), abs_nonneg (c x), hx])
  have hnonneg : 0 ≤ ∫ x, (|c x| - m) ^ 2 ∂S.m := integral_nonneg fun x => sq_nonneg _
  have hexp : ∀ x, (|c x| - m) ^ 2 = c x ^ 2 - (2 * m) * |c x| + m ^ 2 := fun x => by
    rw [sub_sq, sq_abs]
    ring
  have hval : ∫ x, (|c x| - m) ^ 2 ∂S.m = ∫ x, c x ^ 2 ∂S.m - (2 * m) * m + m ^ 2 := by
    simp_rw [hexp]
    rw [integral_add, integral_sub, integral_const_mul, integral_const]
    · rw [← hm_def]
      simp
    · exact hint2
    · exact hint1.const_mul _
    · exact hint2.sub (hint1.const_mul _)
    · exact integrable_const _
  have hfin : phiCorr S D f v = m := rfl
  rw [hfin]
  nlinarith [hnonneg, hval]

/-- The blueprint's `φ` is nonnegative. -/
theorem phiCorr_nonneg (S : MPS.{0}) (D : Factor S) (f : S.X → ℝ) (v : ℕ) :
    0 ≤ phiCorr S D f v :=
  integral_nonneg fun x => abs_nonneg _

/-- **Step 2: the averaged per-shift estimate.**  For `ε ∈ (0, 1]`, there is `H` such that for all
`ℓ` with `H < ε δ^ℓ` the averages over the shifts `h < H` of the absolute window averages of the
correlations `⟨u_{n+h+1}, u_n⟩` over `[M, N-(h+1))` are at most `3ε + √(2ε)`, for all large windows.
-/
theorem shift_average_bound (C : CantorData) (t : ℕ) (hIH : DiffForm C t) {S : MPS.{0}}
    [StandardBorelSpace S.X] (D E : Factor S) (hDE : D.σ ≤ E.σ) (hWM : S.WMHyp D E)
    (s : ℕ → ℕ) (hs : GoodExp s (t + 1)) (f : ℕ → S.X → ℝ)
    (hfE : ∀ j, j < t + 1 → Measurable[E.σ] (f j))
    (hfb : ∀ j, j < t + 1 → ∀ x, |f j x| ≤ 1) (j0 : ℕ) (hj0 : j0 < t + 1)
    (hmean : S.m[f j0 | D.σ] =ᵐ[S.m] 0) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ H : ℕ, 0 < H ∧ ∀ ℓ : ℕ, (H : ℝ) < ε * ((C.delta ^ ℓ : ℕ) : ℝ) →
      ∃ L : ℕ, ∀ M N : ℕ, L ≤ N - M →
        (H : ℝ)⁻¹ * ∑ h ∈ range H,
            |((N - (h + 1) - M : ℕ) : ℝ)⁻¹ * ∑ n ∈ Ico M (N - (h + 1)),
              ∫ x, (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum (n + (h + 1))] x))
                * (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x)) ∂S.m|
          ≤ 3 * ε + Real.sqrt (2 * ε) := by
  have hfj0m : Measurable (f j0) := (hfE j0 hj0).mono E.le le_rfl
  have hfj0b : ∀ x, |f j0 x| ≤ 1 := fun x => hfb j0 hj0 x
  have hcwm : CondWeaklyMixing D (f j0) :=
    hWM (f j0) (hfE j0 hj0) ⟨1, hfj0b⟩ hmean
  haveI := nullSingleton_specMeasure_prod D hfj0m hfj0b hcwm
  have hs1 : 1 ≤ s j0 := hs.1 j0 hj0
  set σ := specMeasure (prodSystem D).koopman
    (toLpC (prodSystem D) (measurable_tensorSq hfj0m) (abs_tensorSq_le hfj0b)) with hσ
  haveI : IsFiniteMeasure σ := (hasSpectralMeasure_specMeasure _ _).isFinite
  obtain ⟨H, hH, hI⟩ := exists_H_small C hs1 σ ε hε0
  refine ⟨H, hH, fun ℓ hℓ => ?_⟩
  set q : ℝ := (C.delta : ℝ) ^ ℓ with hqdef
  have hδpos : (0 : ℝ) < (C.delta : ℝ) := by
    have := C.two_le_delta
    exact_mod_cast (by omega : 0 < C.delta)
  have hqpos : 0 < q := pow_pos hδpos ℓ
  have hcast : ((C.delta ^ ℓ : ℕ) : ℝ) = q := by
    rw [hqdef]
    push_cast
    ring
  rw [hcast] at hℓ
  have hHq : (H : ℝ) < q := by nlinarith
  have hHqN : H < C.delta ^ ℓ := by
    have : (H : ℝ) < ((C.delta ^ ℓ : ℕ) : ℝ) := by rw [hcast]; exact hHq
    exact_mod_cast this
  -- the per-shift estimate for each shift `h + 1 ≤ H`, with a threshold depending on `h`
  have hPS : ∀ h ∈ range H, ∃ L : ℕ, ∀ M N' : ℕ, L ≤ N' - M →
      |((N' - M : ℕ) : ℝ)⁻¹ * ∑ n ∈ Ico M N',
          ∫ x, (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum (n + (h + 1))] x))
            * (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x)) ∂S.m|
        ≤ ε + ((N' - M : ℕ) : ℝ)⁻¹ * ∑ n ∈ Ico M N',
            phiCorr S D (f j0) (s j0 * (C.enum (n + (h + 1)) - C.enum n))
          + ((h + 1 : ℕ) : ℝ) / q + q / ((N' - M : ℕ) : ℝ) := by
    intro h hh
    have hh' : h + 1 < C.delta ^ ℓ := by
      have := Finset.mem_range.1 hh
      omega
    obtain ⟨L, hL⟩ := perShift C t hIH D E hDE hWM s hs f hfE hfb j0 hj0 ℓ (h + 1)
      (Nat.succ_pos h) hh' ε hε0
    exact ⟨L, fun M N' hLN => hL M N' hLN⟩
  choose! Lf hLf using hPS
  set LQ : ℕ := ⌈q / ε⌉₊ with hLQ
  set SL : ℕ := ∑ h ∈ range H, Lf h with hSL
  refine ⟨SL + LQ + 2 * H + 2, fun M N hLN => ?_⟩
  have hNM : 0 < N - M := by omega
  have hNMr : (0 : ℝ) < ((N - M : ℕ) : ℝ) := by exact_mod_cast hNM
  -- each shift satisfies `|A_h| ≤ 3ε + T_h`
  have hA : ∀ h ∈ range H, |((N - (h + 1) - M : ℕ) : ℝ)⁻¹ * ∑ n ∈ Ico M (N - (h + 1)),
      ∫ x, (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum (n + (h + 1))] x))
        * (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x)) ∂S.m|
      ≤ 3 * ε + ((N - (h + 1) - M : ℕ) : ℝ)⁻¹ * ∑ n ∈ Ico M (N - (h + 1)),
          phiCorr S D (f j0) (s j0 * (C.enum (n + (h + 1)) - C.enum n)) := by
    intro h hh
    have hLh : Lf h ≤ SL := Finset.single_le_sum (fun i _ => Nat.zero_le _) hh
    have hwin : Lf h ≤ N - (h + 1) - M ∧ LQ ≤ N - (h + 1) - M := by
      have := Finset.mem_range.1 hh
      omega
    have hbase := hLf h hh M (N - (h + 1)) hwin.1
    have hfirst : ((h + 1 : ℕ) : ℝ) / q ≤ ε := by
      rw [div_le_iff₀ hqpos]
      have hHh : h + 1 ≤ H := by
        have := Finset.mem_range.1 hh
        omega
      have : ((h + 1 : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHh
      nlinarith
    have hLQr : (LQ : ℝ) ≤ ((N - (h + 1) - M : ℕ) : ℝ) := by exact_mod_cast hwin.2
    have hLQpos : (0 : ℝ) < (LQ : ℝ) := by
      rw [hLQ]
      exact_mod_cast Nat.ceil_pos.2 (div_pos hqpos hε0)
    have hsecond : q / ((N - (h + 1) - M : ℕ) : ℝ) ≤ ε := by
      have hNpos : (0 : ℝ) < ((N - (h + 1) - M : ℕ) : ℝ) := lt_of_lt_of_le hLQpos hLQr
      rw [div_le_iff₀ hNpos]
      have hceil : q / ε ≤ (LQ : ℝ) := Nat.le_ceil _
      rw [div_le_iff₀ hε0] at hceil
      nlinarith
    linarith [hbase, hfirst, hsecond]
  -- the spectral bound for the squared correlations, and the Cauchy–Schwarz step
  set ψf : ℕ → ℝ := fun v => ∫ x, (condInner D (f j0 ∘ S.T^[v]) (f j0) x) ^ 2 ∂S.m with hψf
  have hψfour : ∀ v : ℕ, (ψf v : ℂ) = ∫ α, fourier (v : ℤ) α ∂σ :=
    fun v => psi_eq_fourier_prod D hfj0m hfj0b v
  have hψ0 : ∀ v, 0 ≤ ψf v := fun v => integral_nonneg fun x => sq_nonneg _
  have hspec := sum_psi_le_spectral C hs1 σ ψf hψ0 hψfour H M N hH
  have hspec' : ∑ h ∈ range H, ∑ n ∈ Ico M N, ψf (s j0 * (C.enum (n + (h + 1)) - C.enum n))
      ≤ (H : ℝ) * ((N - M : ℕ) : ℝ) * ε := by
    refine le_trans hspec ?_
    have := mul_le_mul_of_nonneg_left hI.le (by positivity : (0 : ℝ) ≤ (H : ℝ) * ((N - M : ℕ) : ℝ))
    exact this
  have hcs := cs_avg_bound H M N hH hNM (fun h => N - (h + 1))
    (fun h _ => Nat.sub_le _ _)
    (fun h hh => by
      have := Finset.mem_range.1 hh
      omega)
    (fun h hh => by
      have := Finset.mem_range.1 hh
      omega)
    (fun h n => phiCorr S D (f j0) (s j0 * (C.enum (n + (h + 1)) - C.enum n)))
    (fun h n => ψf (s j0 * (C.enum (n + (h + 1)) - C.enum n)))
    (fun h n => phiCorr_nonneg S D (f j0) _)
    (fun h n => hψ0 _)
    (fun h n => phiCorr_sq_le_psi D hfj0m hfj0b _)
  set B : ℝ := (H : ℝ)⁻¹ * ∑ h ∈ range H,
      ((((N - (h + 1)) - M : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico M (N - (h + 1)),
        phiCorr S D (f j0) (s j0 * (C.enum (n + (h + 1)) - C.enum n)) with hB
  have hB2 : B ^ 2 ≤ 2 * ε := by
    refine le_trans hcs ?_
    have hHNpos : (0 : ℝ) < (H : ℝ) * ((N - M : ℕ) : ℝ) := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hHNpos]
    nlinarith
  have hBsq : B ≤ Real.sqrt (2 * ε) := le_trans (le_abs_self B) (Real.abs_le_sqrt hB2)
  have hHr : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  calc (H : ℝ)⁻¹ * ∑ h ∈ range H,
          |((N - (h + 1) - M : ℕ) : ℝ)⁻¹ * ∑ n ∈ Ico M (N - (h + 1)),
            ∫ x, (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum (n + (h + 1))] x))
              * (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x)) ∂S.m|
      ≤ (H : ℝ)⁻¹ * ∑ h ∈ range H, (3 * ε + ((N - (h + 1) - M : ℕ) : ℝ)⁻¹
          * ∑ n ∈ Ico M (N - (h + 1)),
            phiCorr S D (f j0) (s j0 * (C.enum (n + (h + 1)) - C.enum n))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h hh => hA h hh)
          (inv_nonneg.2 hHr.le)
    _ = 3 * ε + B := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hB]
        field_simp
    _ ≤ 3 * ε + Real.sqrt (2 * ε) := by linarith [hBsq]

end MPS

end CantorSzemeredi

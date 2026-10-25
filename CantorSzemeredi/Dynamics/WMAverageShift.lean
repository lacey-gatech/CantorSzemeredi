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
    (hNhN : ∀ h, Nh h ≤ N) (hNhM : ∀ h, M ≤ Nh h) (hL : ∀ h, N - M ≤ 2 * (Nh h - M))
    (φ ψ : ℕ → ℕ → ℝ) (hφ0 : ∀ h n, 0 ≤ φ h n) (hψ0 : ∀ h n, 0 ≤ ψ h n)
    (hpsi : ∀ h n, φ h n ^ 2 ≤ ψ h n) :
    ((H : ℝ)⁻¹ * ∑ h ∈ range H,
        (((Nh h - M : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico M (Nh h), φ h n) ^ 2
      ≤ (2 / ((H : ℝ) * ((N - M : ℕ) : ℝ))) * ∑ h ∈ range H, ∑ n ∈ Ico M N, ψ h n := by
  -- the window of `h` has at least half the length of `[M, N)`
  have hLpos : ∀ h, 0 < Nh h - M := fun h => by
    have := hL h
    omega
  have hLr : ∀ h, (0 : ℝ) < ((Nh h - M : ℕ) : ℝ) := fun h => by
    exact_mod_cast hLpos h
  have hNMr : (0 : ℝ) < ((N - M : ℕ) : ℝ) := by exact_mod_cast hN
  -- the square of each window average is at most the window average of `ψ` on `[M, N)`
  have hsq : ∀ h, ((((Nh h - M : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico M (Nh h), φ h n) ^ 2
      ≤ (2 / ((N - M : ℕ) : ℝ)) * ∑ n ∈ Ico M N, ψ h n := by
    intro h
    set L : ℝ := ((Nh h - M : ℕ) : ℝ) with hLdef
    have hcard : (((Ico M (Nh h)).card : ℕ) : ℝ) = L := by
      rw [Nat.card_Ico, hLdef]
    have hcs := sq_sum_le_card_mul_sum_sq (s := Ico M (Nh h)) (f := fun n => φ h n)
    have hcs' : (∑ n ∈ Ico M (Nh h), φ h n) ^ 2 ≤ L * ∑ n ∈ Ico M (Nh h), φ h n ^ 2 := by
      have := hcs
      rw [← hcard]
      exact_mod_cast this
    have hψsub : ∑ n ∈ Ico M (Nh h), ψ h n ≤ ∑ n ∈ Ico M N, ψ h n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (hNhN h))
        fun n _ _ => hψ0 h n
    have hφψ : ∑ n ∈ Ico M (Nh h), φ h n ^ 2 ≤ ∑ n ∈ Ico M N, ψ h n :=
      le_trans (Finset.sum_le_sum fun n _ => hpsi h n)
        (le_trans hψsub le_rfl)
    have hφψ' : ∑ n ∈ Ico M (Nh h), φ h n ^ 2 ≤ ∑ n ∈ Ico M N, ψ h n := by
      refine le_trans (Finset.sum_le_sum fun n _ => hpsi h n) ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (hNhN h))
        fun n _ _ => hψ0 h n
    have hinv : L⁻¹ ≤ 2 / ((N - M : ℕ) : ℝ) := by
      rw [inv_eq_one_div, div_le_div_iff₀ (hLr h) hNMr]
      have : ((N - M : ℕ) : ℝ) ≤ 2 * L := by
        rw [hLdef]
        exact_mod_cast hL h
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
    exact Finset.sum_le_sum fun h _ => hsq h
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

end MPS

end CantorSzemeredi

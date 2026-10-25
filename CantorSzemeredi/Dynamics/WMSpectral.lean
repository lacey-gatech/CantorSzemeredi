/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMPerShift
import CantorSzemeredi.Dynamics.UniformErgodic
import CantorSzemeredi.Cantor.Spectral

/-!
# The spectral bound for the shift average

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`, Step 2, "The spectral bound".
If `ψ(n) = ∫ ⟨T^n f, f⟩_D² dm` is the Fourier transform of the spectral measure `σ` on the circle,
then the sum of `ψ(s(k_{n+h} − k_n))` over `1 ≤ h ≤ H` and `n` in a window is at most
`H (N − M) ∫ Φ_H(sα) dσ(α)`.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Filter Topology

/-- The Fourier character at a lift of `β` is `e(n β)`. -/
theorem fourier_nat_coe (n : ℕ) (β : ℝ) :
    fourier (n : ℤ) (β : AddCircle (1 : ℝ)) = e ((n : ℝ) * β) := by
  rw [fourier_coe_apply]
  unfold e
  congr 1
  push_cast
  ring

/-- The sum over `h < H` and `n ∈ [M,N)` of the characters at a lift `β` is bounded by
`H (N - M) Φ_H(sβ)`. -/
theorem norm_window_sum_le (C : CantorData) (s : ℕ) (H M N : ℕ) (hH : 0 < H) (β : ℝ) :
    ‖∑ h ∈ range H, ∑ n ∈ Ico M N,
        fourier ((s * (C.enum (n + (h + 1)) - C.enum n) : ℕ) : ℤ) (β : AddCircle (1 : ℝ))‖
      ≤ (H : ℝ) * ((N - M : ℕ) : ℝ) * C.Phi H (s * β) := by
  have hterm : ∀ h n, fourier ((s * (C.enum (n + (h + 1)) - C.enum n) : ℕ) : ℤ)
      (β : AddCircle (1 : ℝ)) = e (s * β * C.enum (n + (h + 1))) * e (-(s * β * C.enum n)) := by
    intro h n
    have hle : C.enum n ≤ C.enum (n + (h + 1)) :=
      C.enum_strictMono.monotone (Nat.le_add_right n (h + 1))
    rw [← e_add, fourier_nat_coe]
    congr 1
    push_cast [Nat.cast_sub hle]
    ring
  rw [Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun n _ => hterm h n, Finset.sum_comm]
  have hfac : ∀ n, ∑ h ∈ range H, e (s * β * C.enum (n + (h + 1))) * e (-(s * β * C.enum n))
      = e (-(s * β * C.enum n)) * ∑ h ∈ range H, e (s * β * C.enum (n + (h + 1))) := by
    intro n
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => mul_comm _ _
  rw [Finset.sum_congr rfl fun n _ => hfac n]
  refine le_trans (norm_sum_le _ _) ?_
  have hW : ∀ n, ‖e (-(s * β * C.enum n)) * ∑ h ∈ range H, e (s * β * C.enum (n + (h + 1)))‖
      ≤ (H : ℝ) * C.Phi H (s * β) := by
    intro n
    rw [norm_mul, abs_e, one_mul]
    have hwin : ∑ h ∈ range H, e (s * β * C.enum (n + (h + 1)))
        = ∑ u ∈ Ico (n + 1) (n + 1 + H), e ((s * β) * C.enum u) := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [show n + 1 + h = n + (h + 1) by ring]
    rw [hwin]
    have hHc : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
    have hsplit : ∑ u ∈ Ico (n + 1) (n + 1 + H), e ((s * β) * C.enum u)
        = (H : ℂ) * ((H : ℂ)⁻¹ * ∑ u ∈ Ico (n + 1) (n + 1 + H), e ((s * β) * C.enum u)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hHc, one_mul]
    rw [hsplit, norm_mul, Complex.norm_natCast]
    have key := MPS.window_avg_le_Phi C (s * β) (n + 1) H hH
    have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    exact mul_le_mul_of_nonneg_left key hHnn
  refine le_trans (Finset.sum_le_sum fun n _ => hW n) ?_
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  rw [mul_comm ((H : ℝ)) (C.Phi H (s * β)), ← mul_assoc]
  exact le_of_eq (by ring)

/-- The Fourier characters are integrable against a finite measure. -/
theorem integrable_fourier_nat (σ : Measure Torus) [IsFiniteMeasure σ] (n : ℤ) :
    Integrable (fun α => fourier n α) σ :=
  (integrable_const (1 : ℝ)).mono' (fourier n).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun α => by simp)

/-- **The spectral bound.**  If the Fourier coefficients of `σ` are the nonnegative numbers `ψ(n)`,
then the sum of `ψ(s(k_{n+h+1} - k_n))` over `h < H` and `n ∈ [M,N)` is at most
`H (N-M) ∫ Φ_H(sα) dσ(α)`. -/
theorem sum_psi_le_spectral (C : CantorData) {s : ℕ} (hs : 1 ≤ s) (σ : Measure Torus)
    [IsFiniteMeasure σ] (ψ : ℕ → ℝ) (hψ0 : ∀ n, 0 ≤ ψ n)
    (hψ : ∀ n : ℕ, (ψ n : ℂ) = ∫ α, fourier (n : ℤ) α ∂σ) (H M N : ℕ) (hH : 0 < H) :
    ∑ h ∈ range H, ∑ n ∈ Ico M N, ψ (s * (C.enum (n + (h + 1)) - C.enum n))
      ≤ (H : ℝ) * ((N - M : ℕ) : ℝ) * ∫ α, C.PhiCircle H (s • α) ∂σ := by
  -- the sum as a single integral of characters
  set A : ℝ := ∑ h ∈ range H, ∑ n ∈ Ico M N, ψ (s * (C.enum (n + (h + 1)) - C.enum n)) with hA
  set g : Torus → ℂ := fun α => ∑ h ∈ range H, ∑ n ∈ Ico M N,
      fourier ((s * (C.enum (n + (h + 1)) - C.enum n) : ℕ) : ℤ) α with hg
  have hcomplex : (A : ℂ) = ∫ α, g α ∂σ := by
    rw [hA, hg]
    push_cast
    simp only [hψ]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun h _ => ?_
      rw [integral_finsetSum]
      · rfl
      · exact fun n _ => integrable_fourier_nat σ _
    · exact fun h _ => integrable_finsetSum _ fun n _ => integrable_fourier_nat σ _
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun n _ => hψ0 _
  have hnorm : ‖(A : ℂ)‖ = A := by rw [Complex.norm_real, Real.norm_of_nonneg hAnn]
  have hpt : ∀ α : Torus, ‖g α‖ ≤ (H : ℝ) * ((N - M : ℕ) : ℝ) * C.PhiCircle H (s • α) := by
    intro α
    obtain ⟨β, rfl⟩ := QuotientAddGroup.mk_surjective α
    have hsm : s • (β : AddCircle (1 : ℝ)) = (((s : ℝ) * β : ℝ) : AddCircle (1 : ℝ)) := by
      rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul]
    have hPhi : C.PhiCircle H (s • (β : AddCircle (1 : ℝ))) = C.Phi H ((s : ℝ) * β) := by
      rw [hsm, C.PhiCircle_coe]
    rw [hPhi]
    exact norm_window_sum_le C s H M N hH β
  have hPhiInt : Integrable (fun α : Torus => C.PhiCircle H (s • α)) σ :=
    (integrable_const (1 : ℝ)).mono'
      ((C.measurable_PhiCircle H).comp (measurable_nsmul_addCircle s)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun α => by
        rw [Real.norm_eq_abs, abs_of_nonneg (C.PhiCircle_nonneg H _)]
        exact C.PhiCircle_le_one H _)
  calc A = ‖(A : ℂ)‖ := hnorm.symm
    _ = ‖∫ α, g α ∂σ‖ := by rw [hcomplex]
    _ ≤ ∫ α, ‖g α‖ ∂σ := norm_integral_le_integral_norm _
    _ ≤ ∫ α, (H : ℝ) * ((N - M : ℕ) : ℝ) * C.PhiCircle H (s • α) ∂σ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun α => norm_nonneg _)
          (hPhiInt.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = (H : ℝ) * ((N - M : ℕ) : ℝ) * ∫ α, C.PhiCircle H (s • α) ∂σ := integral_const_mul _ _

/-- As `exists_H_small`, with `H` at least any prescribed bound `K`. -/
theorem exists_H_small_ge (C : CantorData) {s : ℕ} (hs : 1 ≤ s) (σ : Measure Torus)
    [IsFiniteMeasure σ] [NullSingletonClass σ] (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ H : ℕ, K ≤ H ∧ 0 < H ∧ ∫ α, C.PhiCircle H (s • α) ∂σ < ε := by
  have h := C.tendsto_integral_Phi_zero hs σ
  obtain ⟨L0, hL0⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 h).2 ε hε)
  exact ⟨L0 + K + 1, by omega, by omega, hL0 (L0 + K + 1) (by omega)⟩

namespace MPS

/-- The Fourier coefficients of the spectral measure of the relative product are the squared
conditional correlations: `ψ(n) = ∫ ⟨T^n f, f⟩_D² dm`. -/
theorem psi_eq_fourier_prod {S : MPS.{0}} [StandardBorelSpace S.X] (D : Factor S) {f : S.X → ℝ} {C : ℝ}
    (hm : Measurable f) (hb : ∀ x, |f x| ≤ C) (n : ℕ) :
    ((∫ x, (condInner D (f ∘ S.T^[n]) f x) ^ 2 ∂S.m : ℝ) : ℂ)
      = ∫ α, fourier (n : ℤ) α ∂(specMeasure (prodSystem D).koopman
          (toLpC (prodSystem D) (measurable_tensorSq hm) (abs_tensorSq_le hb))) := by
  set P := prodSystem D with hP
  set G := toLpC P (measurable_tensorSq hm) (abs_tensorSq_le hb) with hG
  have hspec := hasSpectralMeasure_specMeasure P.koopman G
  rw [← hspec.inner_eq (n : ℤ), inner_toLpC (S := P) (measurable_tensorSq hm) (abs_tensorSq_le hb) n]
  congr 1
  exact (integral_tensorSq_comp D hm hb n).symm

/-- The spectral measure of the relative product is atomless, when the first factor is
conditionally weakly mixing. -/
theorem nullSingleton_specMeasure_prod {S : MPS.{0}} [StandardBorelSpace S.X] (D : Factor S)
    {f : S.X → ℝ} {C : ℝ}
    (hm : Measurable f) (hb : ∀ x, |f x| ≤ C) (hcwm : CondWeaklyMixing D f) :
    NullSingletonClass (specMeasure (prodSystem D).koopman
      (toLpC (prodSystem D) (measurable_tensorSq hm) (abs_tensorSq_le hb))) :=
  ⟨fun θ => noAtoms_specMeasure_prod_of_condWeaklyMixing D hm hb hcwm θ⟩

/-- **Choice of `H`.**  For an atomless finite measure `σ` on the circle, the averages
`∫ Φ_H(sα) dσ` are below any `ε > 0` for all large `H`. -/
theorem exists_H_small (C : CantorData) {s : ℕ} (hs : 1 ≤ s) (σ : Measure Torus)
    [IsFiniteMeasure σ] [NullSingletonClass σ] (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, 0 < H ∧ ∫ α, C.PhiCircle H (s • α) ∂σ < ε := by
  have h := C.tendsto_integral_Phi_zero hs σ
  obtain ⟨L0, hL0⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 h).2 ε hε)
  exact ⟨L0 + 1, Nat.succ_pos L0, hL0 (L0 + 1) (by omega)⟩

end MPS

end CantorSzemeredi

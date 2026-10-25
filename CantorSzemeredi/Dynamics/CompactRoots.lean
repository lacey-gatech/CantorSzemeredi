/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Cantor.Residues
import CantorSzemeredi.Dynamics.CompactCSZ
import CantorSzemeredi.Dynamics.Localize

/-!
# Systems whose eigenfunctions have roots-of-unity eigenvalues

Blueprint: `blueprint/src/chapter/compact.tex`, `thm:compact-roots-of-unity`.

If the functions `h` with `T^q h = h` for some `q ≥ 1` are dense in `L²`, then for every
`0 ≤ f ≤ 1` the set of indices `n` with `∫ ∏_{s ≤ t} T^{s k_n} f ≥ ∫ f^{t+1} - ε` is syndetic.

The proof approximates `f` by such an invariant `g` in `L¹` (clipped to `[0,1]`), and takes
the indices with `q ∣ k_n`, along which `g` is invariant under all the shifts `T^{s k_n}`.
-/

namespace CantorSzemeredi

open MeasureTheory Filter

namespace MPS

variable {S : MPS}

/-- Clipping to `[0,1]`. -/
noncomputable def clip01 (y : ℝ) : ℝ := min 1 (max 0 y)

theorem clip01_mem (y : ℝ) : 0 ≤ clip01 y ∧ clip01 y ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem clip01_of_mem {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : clip01 y = y := by
  unfold clip01
  rw [max_eq_right h0, min_eq_right h1]

theorem abs_clip01_sub_le (y z : ℝ) : |clip01 y - clip01 z| ≤ |y - z| := by
  unfold clip01
  have h2 : |max 0 y - max 0 z| ≤ |y - z| := by
    rw [max_comm 0 y, max_comm 0 z]
    exact abs_max_sub_max_le_abs y z 0
  have h1 := abs_min_sub_min_le_max (1 : ℝ) (max 0 y) 1 (max 0 z)
  rw [sub_self, abs_zero] at h1
  exact h1.trans (max_le (abs_nonneg _) h2)

/-- If `g ∘ T^q = g` a.e., then `g ∘ T^{qm} = g` a.e. -/
theorem ae_iterate_mul_of_ae {g : S.X → ℝ} {q : ℕ}
    (hg : ∀ᵐ x ∂S.m, g (S.T^[q] x) = g x) (m : ℕ) :
    ∀ᵐ x ∂S.m, g (S.T^[q * m] x) = g x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hcomp := (S.measurePreserving_T_iterate q).quasiMeasurePreserving.ae_eq_comp ih
    filter_upwards [hcomp, hg] with x h1 h2
    have hT : S.T^[q * (m + 1)] x = S.T^[q * m] (S.T^[q] x) := by
      have hq : q * (m + 1) = q * m + q := by ring
      rw [hq, Function.iterate_add_apply]
    rw [hT]
    simp only [Function.comp_apply] at h1 h2
    rw [h1, h2]

/-- Pointwise: `|a^{t+1} - b^{t+1}| ≤ (t+1)|a - b|` for `a, b ∈ [0,1]`. -/
theorem abs_pow_sub_pow_le {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (t : ℕ) :
    |a ^ (t + 1) - b ^ (t + 1)| ≤ (t + 1) * |a - b| := by
  have h := abs_prod_sub_prod_le_sum t (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
  simp only [Finset.prod_const, Finset.card_range, Finset.sum_const, nsmul_eq_mul] at h
  push_cast at h
  exact h

/-- A bounded measurable function is integrable. -/
theorem integrable_of_bdd {φ : S.X → ℝ} (hm : Measurable φ) (hb : ∀ x, |φ x| ≤ 1) :
    Integrable φ S.m :=
  (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)

/-- **Theorem `thm:compact-roots-of-unity`.**  If the functions `h` with `T^q h = h` for some
`q ≥ 1` are dense in `L²`, then for every measurable `0 ≤ f ≤ 1`, every `ε > 0` and every
`t ≥ 0`, the set of indices `n` with `∫ f^{t+1} - ε ≤ ∫ ∏_{s ≤ t} T^{s k_n} f` is syndetic. -/
theorem syndetic_of_rootsOfUnity_spectrum (C : CantorData)
    (hdense : ∀ φ : S.X → ℝ, MemLp φ 2 S.m → ∀ η : ℝ, 0 < η → ∃ h : S.X → ℝ, ∃ q : ℕ,
      1 ≤ q ∧ Measurable h ∧ (∀ᵐ x ∂S.m, h (S.T^[q] x) = h x) ∧
        eLpNorm (φ - h) 2 S.m ≤ ENNReal.ofReal η)
    {f : S.X → ℝ} (hm : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) :
    Syndetic {n : ℕ | ∫ x, f x ^ (t + 1) ∂S.m - ε
      ≤ ∫ x, ∏ s ∈ Finset.range (t + 1), f (S.T^[s * C.enum n] x) ∂S.m} := by
  have hfb : ∀ x, |f x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (h0 x)]
    exact h1 x
  have hfL : MemLp f 2 S.m := MemLp.of_bound hm.aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hfb x)
  set η : ℝ := ε / (2 * (t + 1)) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨h, q, hq1, hhm, hinv, hL2⟩ := hdense f hfL η hη
  -- the clipped invariant approximant `g`
  set g : S.X → ℝ := fun x => clip01 (h x) with hg_def
  have hgm : Measurable g := measurable_const.min (measurable_const.max hhm)
  have hg01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1 := fun x => clip01_mem _
  have hgb : ∀ x, |g x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hg01 x).1]
    exact (hg01 x).2
  have hginv : ∀ᵐ x ∂S.m, g (S.T^[q] x) = g x := hinv.mono fun x hx => by
    simp only [hg_def]
    rw [hx]
  -- the `L¹` distance between `f` and `g`
  have hwm : Measurable (fun x => f x - g x) := hm.sub hgm
  have hwb : ∀ x, |f x - g x| ≤ 1 := fun x => by
    rw [abs_le]
    constructor <;> linarith [h0 x, h1 x, (hg01 x).1, (hg01 x).2]
  have hfhL : MemLp (f - h) 2 S.m := lt_of_le_of_lt hL2 ENNReal.ofReal_lt_top
  have hsq_le : ∀ x, (f x - g x) ^ 2 ≤ (f x - h x) ^ 2 := fun x => by
    have hfx : clip01 (f x) = f x := clip01_of_mem (h0 x) (h1 x)
    have hle : |f x - g x| ≤ |f x - h x| := by
      have := abs_clip01_sub_le (f x) (h x)
      rw [hfx] at this
      exact this
    have := pow_le_pow_left₀ (abs_nonneg _) hle 2
    rwa [sq_abs, sq_abs] at this
  have hsq_int : Integrable (fun x => (f x - g x) ^ 2) S.m :=
    integrable_of_bdd (hwm.pow_const 2) fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have := hwb x
      nlinarith [abs_nonneg (f x - g x), sq_abs (f x - g x)]
  have hsq_mono : ∫ x, (f x - g x) ^ 2 ∂S.m ≤ η ^ 2 := by
    have h1' : ∫ x, (f x - g x) ^ 2 ∂S.m ≤ ∫ x, (f x - h x) ^ 2 ∂S.m :=
      integral_mono hsq_int hfhL.integrable_sq fun x => hsq_le x
    have h2' : ∫ x, (f x - h x) ^ 2 ∂S.m = (eLpNorm (f - h) 2 S.m).toReal ^ 2 :=
      integral_sq_eq_eLpNorm_sq hfhL
    have h3' : (eLpNorm (f - h) 2 S.m).toReal ≤ η :=
      ENNReal.toReal_le_of_le_ofReal hη.le hL2
    have h4' : (eLpNorm (f - h) 2 S.m).toReal ^ 2 ≤ η ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg h3' 2
    linarith
  -- `∫ |f - g| ≤ η`, from `|w| ≤ (w^2 + η^2)/(2η)`
  have habs_int : Integrable (fun x => |f x - g x|) S.m :=
    integrable_of_bdd hwm.abs fun x => by
      rw [abs_abs]
      exact hwb x
  have hw_abs : ∫ x, |f x - g x| ∂S.m ≤ η := by
    have hpt : ∀ x, |f x - g x| ≤ ((f x - g x) ^ 2 + η ^ 2) / (2 * η) := fun x => by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_abs (f x - g x), sq_nonneg (|f x - g x| - η)]
    have hI1 := habs_int
    have hI2 : Integrable (fun x => ((f x - g x) ^ 2 + η ^ 2) / (2 * η)) S.m :=
      (hsq_int.add (integrable_const _)).div_const _
    have hmono := integral_mono hI1 hI2 fun x => hpt x
    rw [integral_div, integral_add hsq_int (integrable_const _), integral_const] at hmono
    simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
    have hb : (∫ x, (f x - g x) ^ 2 ∂S.m + η ^ 2) / (2 * η) ≤ η := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hsq_mono]
    linarith
  -- shifts preserve the `L¹` distance
  have hshift : ∀ m : ℕ, ∫ x, |f (S.T^[m] x) - g (S.T^[m] x)| ∂S.m = ∫ x, |f x - g x| ∂S.m := by
    intro m
    have hmp : MeasurePreserving (S.equivPow m) S.m S.m := by
      rw [coe_equivPow]
      exact S.measurePreserving_T_iterate m
    have := hmp.integral_comp' (fun x => |f x - g x|)
    rw [coe_equivPow] at this
    exact this
  -- the pointwise estimate along a fixed index `n` with `q ∣ k_n`
  have hmem : ∀ n : ℕ, q ∣ C.enum n → ∫ x, f x ^ (t + 1) ∂S.m - ε
      ≤ ∫ x, ∏ s ∈ Finset.range (t + 1), f (S.T^[s * C.enum n] x) ∂S.m := by
    intro n hdvd
    obtain ⟨c, hc⟩ := hdvd
    -- along the shifts `s k_n`, the approximant is invariant almost everywhere
    have hinv_s : ∀ᵐ x ∂S.m, ∀ s : ℕ, g (S.T^[s * C.enum n] x) = g x := by
      rw [ae_all_iff]
      intro s
      have hsk : s * C.enum n = q * (s * c) := by rw [hc]; ring
      rw [hsk]
      exact ae_iterate_mul_of_ae hginv (s * c)
    have hgprod : ∫ x, ∏ s ∈ Finset.range (t + 1), g (S.T^[s * C.enum n] x) ∂S.m
        = ∫ x, g x ^ (t + 1) ∂S.m := by
      refine integral_congr_ae (hinv_s.mono fun x hx => ?_)
      dsimp only
      rw [Finset.prod_congr rfl fun s _ => hx s, Finset.prod_const, Finset.card_range]
    -- telescoping: `∏ f∘T^{sk} ≥ ∏ g∘T^{sk} - ∑ |f∘T^{sk} - g∘T^{sk}|`
    have hpt : ∀ x, ∏ s ∈ Finset.range (t + 1), g (S.T^[s * C.enum n] x)
        - ∑ s ∈ Finset.range (t + 1), |f (S.T^[s * C.enum n] x) - g (S.T^[s * C.enum n] x)|
        ≤ ∏ s ∈ Finset.range (t + 1), f (S.T^[s * C.enum n] x) := fun x => by
      have := abs_prod_sub_prod_le_sum t (fun s => f (S.T^[s * C.enum n] x))
        (fun s => g (S.T^[s * C.enum n] x)) (fun s => ⟨h0 _, h1 _⟩) (fun s => hg01 _)
      have h' := (abs_le.1 this).1
      linarith
    have hprodf_int : Integrable (fun x => ∏ s ∈ Finset.range (t + 1),
        f (S.T^[s * C.enum n] x)) S.m :=
      integrable_of_bdd (Finset.measurable_prod _ fun s _ => hm.comp (S.measurable_T.iterate _))
        fun x => by
          rw [abs_of_nonneg (Finset.prod_nonneg fun s _ => h0 _)]
          exact Finset.prod_le_one₀ (fun s _ => h0 _) fun s _ => h1 _
    have hprodg_int : Integrable (fun x => ∏ s ∈ Finset.range (t + 1),
        g (S.T^[s * C.enum n] x)) S.m :=
      integrable_of_bdd (Finset.measurable_prod _ fun s _ => hgm.comp (S.measurable_T.iterate _))
        fun x => by
          rw [abs_of_nonneg (Finset.prod_nonneg fun s _ => (hg01 _).1)]
          exact Finset.prod_le_one₀ (fun s _ => (hg01 _).1) fun s _ => (hg01 _).2
    have hterm_int : ∀ s : ℕ, Integrable (fun x =>
        |f (S.T^[s * C.enum n] x) - g (S.T^[s * C.enum n] x)|) S.m := fun s =>
      integrable_of_bdd ((hwm.comp (S.measurable_T.iterate _)).abs) fun x => by
        rw [abs_abs]
        exact hwb _
    have hsum_int : Integrable (fun x => ∑ s ∈ Finset.range (t + 1),
        |f (S.T^[s * C.enum n] x) - g (S.T^[s * C.enum n] x)|) S.m :=
      integrable_finsetSum _ fun s _ => hterm_int s
    have hsum_eq : ∫ x, ∑ s ∈ Finset.range (t + 1),
        |f (S.T^[s * C.enum n] x) - g (S.T^[s * C.enum n] x)| ∂S.m
        = (t + 1) * ∫ x, |f x - g x| ∂S.m := by
      rw [integral_finsetSum _ fun s _ => hterm_int s]
      simp only [hshift, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    -- the lower bound for the product integral
    have hlow1 : ∫ x, g x ^ (t + 1) ∂S.m - (t + 1) * ∫ x, |f x - g x| ∂S.m
        ≤ ∫ x, ∏ s ∈ Finset.range (t + 1), f (S.T^[s * C.enum n] x) ∂S.m := by
      rw [← hgprod, ← hsum_eq, ← integral_sub hprodg_int hsum_int]
      exact integral_mono (hprodg_int.sub hsum_int) hprodf_int hpt
    -- the power estimate `∫ f^{t+1} - ∫ g^{t+1} ≤ (t+1) ∫ |f - g|`
    have hpow_int : Integrable (fun x => f x ^ (t + 1)) S.m :=
      integrable_of_bdd (hm.pow_const _) fun x => by
        rw [abs_of_nonneg (pow_nonneg (h0 x) _)]
        exact pow_le_one₀ (h0 x) (h1 x)
    have hgpow_int : Integrable (fun x => g x ^ (t + 1)) S.m :=
      integrable_of_bdd (hgm.pow_const _) fun x => by
        rw [abs_of_nonneg (pow_nonneg (hg01 x).1 _)]
        exact pow_le_one₀ (hg01 x).1 (hg01 x).2
    have hpow_le : ∫ x, f x ^ (t + 1) ∂S.m - ∫ x, g x ^ (t + 1) ∂S.m
        ≤ (t + 1) * ∫ x, |f x - g x| ∂S.m := by
      have hp : ∀ x, f x ^ (t + 1) - g x ^ (t + 1) ≤ (t + 1) * |f x - g x| := fun x =>
        le_trans (le_abs_self _) (abs_pow_sub_pow_le ⟨h0 x, h1 x⟩ (hg01 x) t)
      calc ∫ x, f x ^ (t + 1) ∂S.m - ∫ x, g x ^ (t + 1) ∂S.m
          = ∫ x, (f x ^ (t + 1) - g x ^ (t + 1)) ∂S.m := (integral_sub hpow_int hgpow_int).symm
        _ ≤ ∫ x, (t + 1) * |f x - g x| ∂S.m :=
            integral_mono (hpow_int.sub hgpow_int) (habs_int.const_mul _) hp
        _ = (t + 1) * ∫ x, |f x - g x| ∂S.m := integral_const_mul _ _
    -- combine: `∫ ∏ f ≥ ∫ f^{t+1} - 2(t+1) η = ∫ f^{t+1} - ε`
    have hεη : 2 * (t + 1) * η = ε := by
      rw [hη_def]
      field_simp
    have hwη : (t + 1) * ∫ x, |f x - g x| ∂S.m ≤ (t + 1) * η :=
      mul_le_mul_of_nonneg_left hw_abs (by positivity)
    linarith [hlow1, hpow_le, hwη, hεη]
  -- the indices with `q ∣ k_n` form a syndetic set
  have hsyn : Syndetic {n : ℕ | q ∣ C.enum n} := C.syndetic_dvd_enum q (by omega)
  obtain ⟨L, hL⟩ := hsyn
  exact ⟨L, fun n => by
    obtain ⟨k, hk, hk1, hk2⟩ := hL n
    exact ⟨k, hmem k hk, hk1, hk2⟩⟩

end MPS

end CantorSzemeredi

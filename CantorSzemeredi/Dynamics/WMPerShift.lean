/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMCorr
import CantorSzemeredi.Dynamics.WMAverage
import CantorSzemeredi.Cantor.Residues

/-!
# The per-shift estimate

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`, Step 1, eq. `per-shift`.
For a fixed shift `1 ≤ h < δ^ℓ`, the averages over windows `[M,N)` of the correlations
`⟨u_{n+h}, u_n⟩`, where `u_n = ∏_j f_j(T^{s_j k_n} ·)`, are bounded by the averages of
`φ(s_{j0}(k_{n+h} - k_n))` plus small errors.  The residue decomposition splits the window into
the good residue classes (on which `k_{n+h} - k_n` is constant on each class, by
`enum_sub_enum_eq`) and the bad set, whose size is controlled by `card_goodResidues_ge`.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Filter Topology

namespace MPS

/-- The correlation identity on a residue class: the correlation of `u_{n+Δ}` and `u_n` is the
integral of the product of the shifted factors `F_j = f_j · T^{s_j Δ} f_j`, with the shifts
`(s_j - s_0) k_n`. -/
theorem corr_eq_F (S : MPS.{0}) (s : ℕ → ℕ) (t : ℕ) (hs : GoodExp s (t + 1))
    (f : ℕ → S.X → ℝ) (k Δ : ℕ) :
    ∫ x, (∏ j ∈ range (t + 1), f j (S.T^[s j * (k + Δ)] x))
        * (∏ j ∈ range (t + 1), f j (S.T^[s j * k] x)) ∂S.m
      = ∫ x, ∏ j ∈ range (t + 1),
          (fun y => f j y * f j (S.T^[s j * Δ] y)) (S.T^[(s j - s 0) * k] x) ∂S.m := by
  rw [integral_corr_eq_shifted S s (t + 1) hs f k Δ]
  simp only [Nat.sub_mul]

/-- A product of functions bounded by `1` in modulus is bounded by `1`. -/
theorem abs_prod_le_one_of {ι : Type*} (I : Finset ι) (g : ι → ℝ) (hg : ∀ i ∈ I, |g i| ≤ 1) :
    |∏ i ∈ I, g i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) hg

/-- The correlation of two functions bounded by `1` is bounded by `1`. -/
theorem abs_integral_mul_le_one {S : MPS.{0}} {g h : S.X → ℝ} (hg : ∀ x, |g x| ≤ 1)
    (hh : ∀ x, |h x| ≤ 1) : |∫ x, g x * h x ∂S.m| ≤ 1 := by
  refine le_trans abs_integral_le_integral_abs ?_
  have h1 : ∫ x, |g x * h x| ∂S.m ≤ ∫ x, (1 : ℝ) ∂S.m := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (integrable_const 1) (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [abs_mul]
    exact mul_le_one₀ (hg x) (abs_nonneg _) (hh x)
  simpa using h1

/-- The residue-class bad set has at most `(h/q)(N-M) + q` elements. -/
theorem card_bad_le (C : CantorData) (ℓ h M N : ℕ) (hh : h < C.delta ^ ℓ) (hMN : M ≤ N) :
    (((Ico M N).filter (fun n => ¬ (n % C.delta ^ ℓ + h < C.delta ^ ℓ))).card : ℝ)
      ≤ (h : ℝ) / (C.delta ^ ℓ : ℝ) * ((N : ℝ) - M) + (C.delta ^ ℓ : ℝ) := by
  have hG := C.card_goodResidues_ge h ℓ M N hh
  have hsplit := Finset.card_filter_add_card_filter_not (s := Ico M N)
    (fun n => n % C.delta ^ ℓ + h < C.delta ^ ℓ)
  rw [Nat.card_Ico] at hsplit
  have hcast : ((Ico M N).filter (fun n => n % C.delta ^ ℓ + h < C.delta ^ ℓ)).card
      + ((Ico M N).filter (fun n => ¬ (n % C.delta ^ ℓ + h < C.delta ^ ℓ))).card = N - M := hsplit
  have hcast' : (((Ico M N).filter (fun n => n % C.delta ^ ℓ + h < C.delta ^ ℓ)).card : ℝ)
      + (((Ico M N).filter (fun n => ¬ (n % C.delta ^ ℓ + h < C.delta ^ ℓ))).card : ℝ)
      = (N : ℝ) - M := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hcast
    simp only [Nat.cast_add] at this
    rw [this, Nat.cast_sub hMN]
  have hq : (0 : ℝ) < (C.delta ^ ℓ : ℝ) := by
    have : 0 < C.delta ^ ℓ := Nat.pow_pos (by have := C.two_le_delta; omega)
    exact_mod_cast this
  have hdiv : (1 - (h : ℝ) / (C.delta : ℝ) ^ ℓ) * ((N : ℝ) - M) - (C.delta : ℝ) ^ ℓ ≤
      (((Ico M N).filter (fun n => n % C.delta ^ ℓ + h < C.delta ^ ℓ)).card : ℝ) := hG
  have hpow : ((C.delta : ℝ) ^ ℓ) = (C.delta ^ ℓ : ℝ) := by push_cast; rfl
  rw [hpow] at hdiv
  have key : (h : ℝ) / (C.delta ^ ℓ : ℝ) * ((N : ℝ) - M)
      = ((N : ℝ) - M) - (1 - (h : ℝ) / (C.delta ^ ℓ : ℝ)) * ((N : ℝ) - M) := by ring
  linarith

/-- The factor `F^{(Δ)}_j = f_j · T^{s_j Δ} f_j` is `E`-measurable and bounded by `1`. -/
theorem measurable_F_shift {S : MPS.{0}} {E : Factor S} (s : ℕ → ℕ) (f : ℕ → S.X → ℝ)
    (hfE : ∀ j, j < t → Measurable[E.σ] (f j)) (Δ j : ℕ) (hj : j < t) :
    Measurable[E.σ] (fun y => f j y * f j (S.T^[s j * Δ] y)) :=
  (hfE j hj).mul (measurable_comp_iter E (hfE j hj) _)

/-- **Per-class bound.**  On a residue class `c` of `n` modulo `q = δ^ℓ`, where `k_{n+h} = k_n + Δ`
is constant, the correlations `⟨u_{n+h}, u_n⟩` over the class sum to at most `K η` plus the sum of
`φ(s_{j0}(k_{n+h} - k_n))`, provided the `W`-term for the factors `F_j = f_j · T^{s_j Δ} f_j`
is below `η` in `L¹`. -/
theorem class_corr_bound (C : CantorData) (s : ℕ → ℕ) (t : ℕ) (hs : GoodExp s (t + 1))
    {S : MPS.{0}} (D : Factor S) (f : ℕ → S.X → ℝ) (hfm : ∀ j, j < t + 1 → Measurable (f j))
    (hfb : ∀ j, j < t + 1 → ∀ x, |f j x| ≤ 1) (j0 : ℕ) (hj0 : j0 < t + 1)
    (h ℓ c M N Δ : ℕ) (hΔ : ∀ n, n % C.delta ^ ℓ = c → C.enum (n + h) = C.enum n + Δ) (η : ℝ)
    (hw : ∫ x, |((((Ico M N).filter (fun n => n % C.delta ^ ℓ = c)).card : ℝ))⁻¹
        * ∑ n ∈ (Ico M N).filter (fun n => n % C.delta ^ ℓ = c),
            (∏ i ∈ range t, (fun y => f (i + 1) y * f (i + 1) (S.T^[s (i + 1) * Δ] y))
                (S.T^[(s (i + 1) - s 0) * C.enum n] x)
              - ∏ i ∈ range t, (S.m[(fun y => f (i + 1) y * f (i + 1) (S.T^[s (i + 1) * Δ] y))
                  | D.σ]) (S.T^[(s (i + 1) - s 0) * C.enum n] x))|
        ∂S.m < η) :
    |∑ n ∈ (Ico M N).filter (fun n => n % C.delta ^ ℓ = c),
        ∫ x, (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum (n + h)] x))
          * (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x)) ∂S.m|
      ≤ (((Ico M N).filter (fun n => n % C.delta ^ ℓ = c)).card : ℝ) * η
        + ∑ n ∈ (Ico M N).filter (fun n => n % C.delta ^ ℓ = c),
            phiCorr S D (f j0) (s j0 * (C.enum (n + h) - C.enum n)) := by
  set I := (Ico M N).filter (fun n => n % C.delta ^ ℓ = c) with hI
  set F : ℕ → S.X → ℝ := fun j y => f j y * f j (S.T^[s j * Δ] y) with hF
  have hΔn : ∀ n ∈ I, C.enum (n + h) - C.enum n = Δ := by
    intro n hn
    have := hΔ n (mem_filter.1 hn).2
    omega
  have hcorr : ∑ n ∈ I, ∫ x, (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum (n + h)] x))
        * (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x)) ∂S.m
      = ∑ n ∈ I, ∫ x, ∏ j ∈ range (t + 1), F j (S.T^[(s j - s 0) * C.enum n] x) ∂S.m :=
    Finset.sum_congr rfl fun n hn => by
      rw [hΔ n (mem_filter.1 hn).2]
      exact corr_eq_F S s t hs f (C.enum n) Δ
  have hFm : ∀ j, j < t + 1 → Measurable (F j) := fun j hj =>
    (hfm j hj).mul ((hfm j hj).comp (S.measurable_T.iterate _))
  have hFb : ∀ j, j < t + 1 → ∀ x, |F j x| ≤ 1 := fun j hj x => by
    rw [hF]
    dsimp only
    rw [abs_mul]
    exact mul_le_one₀ (hfb j hj x) (abs_nonneg _) (hfb j hj _)
  have hav := abs_average_corr_le s t hs D F hFm hFb I C.enum j0 hj0
  have hphi : ∫ x, |S.m[F j0 | D.σ] x| ∂S.m = phiCorr S D (f j0) (s j0 * Δ) :=
    integral_abs_condExp_factor S D s f Δ j0
  have hφsum : ∑ n ∈ I, phiCorr S D (f j0) (s j0 * (C.enum (n + h) - C.enum n))
      = (I.card : ℝ) * phiCorr S D (f j0) (s j0 * Δ) := by
    rw [Finset.sum_congr rfl fun n hn => by rw [hΔn n hn], Finset.sum_const, nsmul_eq_mul]
  rw [hcorr, hφsum]
  by_cases hI0 : I.card = 0
  · have hη : 0 ≤ η := le_of_lt (lt_of_le_of_lt (integral_nonneg fun x => abs_nonneg _) hw)
    rw [Finset.card_eq_zero.1 hI0]
    simp [hη]
  have hK : (0 : ℝ) < (I.card : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hI0)
  have hbound : |((I.card : ℝ))⁻¹ * ∑ n ∈ I, ∫ x, ∏ j ∈ range (t + 1), F j (S.T^[(s j - s 0) * C.enum n] x) ∂S.m|
      ≤ η + phiCorr S D (f j0) (s j0 * Δ) := by
    refine le_trans hav ?_
    rw [← hphi]
    exact add_le_add hw.le le_rfl
  have habs : |∑ n ∈ I, ∫ x, ∏ j ∈ range (t + 1), F j (S.T^[(s j - s 0) * C.enum n] x) ∂S.m|
      = (I.card : ℝ) * |((I.card : ℝ))⁻¹ * ∑ n ∈ I, ∫ x, ∏ j ∈ range (t + 1), F j (S.T^[(s j - s 0) * C.enum n] x) ∂S.m| := by
    conv_lhs => rw [← mul_inv_cancel_left₀ hK.ne' (∑ n ∈ I, ∫ x, ∏ j ∈ range (t + 1), F j (S.T^[(s j - s 0) * C.enum n] x) ∂S.m)]
    rw [abs_mul, abs_of_pos hK]
  rw [habs]
  calc (I.card : ℝ) * |((I.card : ℝ))⁻¹ * ∑ n ∈ I, ∫ x, ∏ j ∈ range (t + 1), F j (S.T^[(s j - s 0) * C.enum n] x) ∂S.m|
      ≤ (I.card : ℝ) * (η + phiCorr S D (f j0) (s j0 * Δ)) :=
        mul_le_mul_of_nonneg_left hbound hK.le
    _ = (I.card : ℝ) * η + (I.card : ℝ) * phiCorr S D (f j0) (s j0 * Δ) := by ring

/-- The residue split of a window: the good classes `c < q - h` and the bad set. -/
theorem sum_split_residues (q h M N : ℕ) (hh : h < q) (g : ℕ → ℝ) :
    ∑ n ∈ Ico M N, g n
      = ∑ c ∈ range (q - h), ∑ n ∈ (Ico M N).filter (fun n => n % q = c), g n
        + ∑ n ∈ (Ico M N).filter (fun n => ¬ (n % q + h < q)), g n := by
  rw [← Finset.sum_filter_add_sum_filter_not (Ico M N) (fun n => n % q + h < q) g]
  congr 1
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Ico M N).filter (fun n => n % q + h < q))
    (t := range (q - h)) (g := fun n => n % q) (fun n hn => by
      rw [Finset.mem_range]
      have := (Finset.mem_filter.1 hn).2
      omega)]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Finset.mem_range] at hc
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hn, _⟩, hcn⟩
    exact ⟨hn, hcn⟩
  · rintro ⟨hn, hcn⟩
    exact ⟨⟨hn, by omega⟩, hcn⟩

/-- Along a residue class `c` with `c + h < q`, the shift `k_{n+h} − k_n` is constant. -/
theorem enum_add_of_class (C : CantorData) (ℓ h c : ℕ) (hc : c + h < C.delta ^ ℓ) (n : ℕ)
    (hn : n % C.delta ^ ℓ = c) :
    C.enum (n + h) = C.enum n + (C.enum (c + h) - C.enum c) := by
  have h1 := C.enum_sub_enum_eq (ℓ := ℓ) (h := h) (n := n) (c := c) hn hc
  have h2 : C.enum c ≤ C.enum (c + h) := C.enum_strictMono.monotone (Nat.le_add_right c h)
  omega

/-- The residue assembly: from the per-class bounds and the count of the bad set, the sum over a
window is bounded by `η · (N - M)`, plus the sum of `Φ` over the window, plus the bad count. -/
theorem assemble_bound (q h M N : ℕ) (hh : h < q) (hMN : M ≤ N) (g Φ : ℕ → ℝ) (η : ℝ)
    (hη : 0 ≤ η) (hg : ∀ n, |g n| ≤ 1) (hΦ : ∀ n, 0 ≤ Φ n)
    (hbad : (((Ico M N).filter (fun n => ¬ (n % q + h < q))).card : ℝ)
      ≤ (h : ℝ) / (q : ℝ) * ((N - M : ℕ) : ℝ) + (q : ℝ))
    (hcls : ∀ c ∈ range (q - h),
      |∑ n ∈ (Ico M N).filter (fun n => n % q = c), g n|
        ≤ (((Ico M N).filter (fun n => n % q = c)).card : ℝ) * η
          + ∑ n ∈ (Ico M N).filter (fun n => n % q = c), Φ n) :
    |∑ n ∈ Ico M N, g n|
      ≤ η * ((N - M : ℕ) : ℝ) + ∑ n ∈ Ico M N, Φ n + (h : ℝ) / (q : ℝ) * ((N - M : ℕ) : ℝ)
        + (q : ℝ) := by
  rw [sum_split_residues q h M N hh g]
  -- the class counts add up to at most the window length
  have hcount : ∑ c ∈ range (q - h), (((Ico M N).filter (fun n => n % q = c)).card : ℝ)
      ≤ ((N - M : ℕ) : ℝ) := by
    have hs := sum_split_residues q h M N hh (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico] at hs
    have hbad0 : (0 : ℝ) ≤ ((Ico M N).filter (fun n => ¬ (n % q + h < q)) |>.card : ℝ) :=
      Nat.cast_nonneg _
    have : ∑ c ∈ range (q - h), (((Ico M N).filter (fun n => n % q = c)).card : ℝ)
        = ∑ c ∈ range (q - h), ∑ n ∈ (Ico M N).filter (fun n => n % q = c), (1 : ℝ) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      simp
    rw [this]
    linarith
  -- the sums of `Φ` over the good classes are bounded by the sum over the window
  have hphi : ∑ c ∈ range (q - h), ∑ n ∈ (Ico M N).filter (fun n => n % q = c), Φ n
      ≤ ∑ n ∈ Ico M N, Φ n := by
    have hs := sum_split_residues q h M N hh Φ
    have hbadΦ : 0 ≤ ∑ n ∈ (Ico M N).filter (fun n => ¬ (n % q + h < q)), Φ n :=
      Finset.sum_nonneg fun n _ => hΦ n
    linarith
  -- the bad part of the sum
  have hbadsum : |∑ n ∈ (Ico M N).filter (fun n => ¬ (n % q + h < q)), g n|
      ≤ (((Ico M N).filter (fun n => ¬ (n % q + h < q))).card : ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun n _ => hg n) ?_
    simp
  -- the good part of the sum, class by class
  have hgood : |∑ c ∈ range (q - h), ∑ n ∈ (Ico M N).filter (fun n => n % q = c), g n|
      ≤ η * ∑ c ∈ range (q - h), (((Ico M N).filter (fun n => n % q = c)).card : ℝ)
        + ∑ c ∈ range (q - h), ∑ n ∈ (Ico M N).filter (fun n => n % q = c), Φ n := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun c hc => ?_
    have := hcls c hc
    linarith [mul_comm η (((Ico M N).filter (fun n => n % q = c)).card : ℝ)]
  have hη' : η * ∑ c ∈ range (q - h), (((Ico M N).filter (fun n => n % q = c)).card : ℝ)
      ≤ η * ((N - M : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hcount hη
  calc |∑ c ∈ range (q - h), ∑ n ∈ (Ico M N).filter (fun n => n % q = c), g n
        + ∑ n ∈ (Ico M N).filter (fun n => ¬ (n % q + h < q)), g n|
      ≤ |∑ c ∈ range (q - h), ∑ n ∈ (Ico M N).filter (fun n => n % q = c), g n|
        + |∑ n ∈ (Ico M N).filter (fun n => ¬ (n % q + h < q)), g n| := abs_add_le _ _
    _ ≤ η * ((N - M : ℕ) : ℝ) + ∑ n ∈ Ico M N, Φ n + (h : ℝ) / (q : ℝ) * ((N - M : ℕ) : ℝ)
        + (q : ℝ) := by linarith

/-- **The per-shift estimate** (blueprint `per-shift`).  For a fixed shift `1 ≤ h < δ^ℓ`, the
averages over windows `[M,N)` of the correlations `⟨u_{n+h}, u_n⟩` are bounded by the averages of
`φ(s_{j0}(k_{n+h} - k_n))` plus `η`, `h/δ^ℓ`, and `δ^ℓ/(N-M)`, once `N - M` is large. -/
theorem perShift (C : CantorData) (t : ℕ) (hIH : DiffForm C t) {S : MPS.{0}}
    [StandardBorelSpace S.X] (D E : Factor S)
    (hDE : D.σ ≤ E.σ) (hWM : S.WMHyp D E) (s : ℕ → ℕ) (hs : GoodExp s (t + 1))
    (f : ℕ → S.X → ℝ) (hfE : ∀ j, j < t + 1 → Measurable[E.σ] (f j))
    (hfb : ∀ j, j < t + 1 → ∀ x, |f j x| ≤ 1) (j0 : ℕ) (hj0 : j0 < t + 1)
    (ℓ h : ℕ) (hh : 0 < h) (hhq : h < C.delta ^ ℓ) (η : ℝ) (hη : 0 < η) :
    ∃ L : ℕ, ∀ M N : ℕ, L ≤ N - M →
      |((N - M : ℕ) : ℝ)⁻¹ * ∑ n ∈ Ico M N,
          ∫ x, (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum (n + h)] x))
            * (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x)) ∂S.m|
        ≤ η + ((N - M : ℕ) : ℝ)⁻¹ * ∑ n ∈ Ico M N,
            phiCorr S D (f j0) (s j0 * (C.enum (n + h) - C.enum n))
          + (h : ℝ) / (C.delta ^ ℓ : ℝ) + (C.delta ^ ℓ : ℝ) / ((N - M : ℕ) : ℝ) := by
  set q := C.delta ^ ℓ with hq
  have hqR : (C.delta : ℝ) ^ ℓ = (q : ℝ) := by
    rw [hq]
    push_cast
    ring
  -- the `W`-term of each good class tends to zero along the uniform filter
  have hT : ∀ c ∈ range (q - h), Tendsto (fun p : ℕ × ℕ => ∫ x,
      |((((Ico p.1 p.2).filter (fun n => n % q = c)).card : ℝ))⁻¹
        * ∑ n ∈ (Ico p.1 p.2).filter (fun n => n % q = c),
            (∏ i ∈ range t, (fun y => f (i + 1) y * f (i + 1) (S.T^[s (i + 1) * (C.enum (c + h) - C.enum c)] y))
                (S.T^[(s (i + 1) - s 0) * C.enum n] x)
              - ∏ i ∈ range t, (S.m[(fun y => f (i + 1) y * f (i + 1)
                  (S.T^[s (i + 1) * (C.enum (c + h) - C.enum c)] y)) | D.σ])
                    (S.T^[(s (i + 1) - s 0) * C.enum n] x))|
        ∂S.m) uniformFilter (𝓝 0) := by
    intro c hc
    rw [Finset.mem_range] at hc
    refine tendsto_integral_abs_wClass C t hIH S s hs D E hDE hWM ℓ c (by omega)
      (fun j y => f j y * f j (S.T^[s j * (C.enum (c + h) - C.enum c)] y)) 1 zero_le_one
      (fun j hj => (hfE j hj).mul (measurable_comp_iter E (hfE j hj) _))
      (fun j hj x => by
        rw [abs_mul]
        exact mul_le_one₀ (hfb j hj x) (abs_nonneg _) (hfb j hj _))
  obtain ⟨L1, hL1⟩ := mem_uniformFilter_iff.1
    ((Filter.eventually_all_finset (range (q - h))).2 fun c hc => (tendsto_order.1 (hT c hc)).2 η hη)
  refine ⟨L1 + 1, fun M N hLN => ?_⟩
  have hMN : M ≤ N := by omega
  have hpos : 0 < N - M := by omega
  have hposR : (0 : ℝ) < ((N - M : ℕ) : ℝ) := by exact_mod_cast hpos
  have hfm : ∀ j, j < t + 1 → Measurable (f j) := fun j hj => (hfE j hj).mono E.le le_rfl
  set g : ℕ → ℝ := fun n => ∫ x, (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum (n + h)] x))
    * (∏ j ∈ range (t + 1), f j (S.T^[s j * C.enum n] x)) ∂S.m with hgdef
  set Φ : ℕ → ℝ := fun n => phiCorr S D (f j0) (s j0 * (C.enum (n + h) - C.enum n)) with hΦdef
  have hg : ∀ n, |g n| ≤ 1 := fun n =>
    abs_integral_mul_le_one (fun x => abs_prod_le_one_of _ _ fun j hj => hfb j (mem_range.1 hj) _)
      (fun x => abs_prod_le_one_of _ _ fun j hj => hfb j (mem_range.1 hj) _)
  have hΦ : ∀ n, 0 ≤ Φ n := fun n => integral_nonneg fun x => abs_nonneg _
  have hbad : (((Ico M N).filter (fun n => ¬ (n % q + h < q))).card : ℝ)
      ≤ (h : ℝ) / (q : ℝ) * ((N - M : ℕ) : ℝ) + (q : ℝ) := by
    have := card_bad_le C ℓ h M N hhq hMN
    rw [← Nat.cast_sub hMN, hqR] at this
    exact this
  have hm := hL1 M N (by omega)
  have hcls : ∀ c ∈ range (q - h),
      |∑ n ∈ (Ico M N).filter (fun n => n % q = c), g n|
        ≤ (((Ico M N).filter (fun n => n % q = c)).card : ℝ) * η
          + ∑ n ∈ (Ico M N).filter (fun n => n % q = c), Φ n := by
    intro c hc
    have hc' : c + h < q := by
      rw [Finset.mem_range] at hc
      omega
    have hlt := hm c hc
    exact class_corr_bound C s t hs D f hfm hfb j0 hj0 h ℓ c M N (C.enum (c + h) - C.enum c)
      (fun n hn => enum_add_of_class C ℓ h c hc' n hn) η hlt
  have key := assemble_bound q h M N hhq hMN g Φ η hη.le hg hΦ hbad hcls
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hposR.le), hqR]
  refine le_trans (mul_le_mul_of_nonneg_left key (inv_nonneg.2 hposR.le)) (le_of_eq ?_)
  field_simp

end MPS

end CantorSzemeredi

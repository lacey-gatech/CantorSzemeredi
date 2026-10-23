/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Basic

/-!
# Spectral measures of a unitary

Blueprint: `def:spectral-measure` and `lem:wiener` in `blueprint/src/chapter/mps.tex`.

For a unitary `U` on a complex Hilbert space and a vector `v`, the spectral measure `σ_v` is
the finite positive Borel measure on `𝕋 = ℝ/ℤ` with

  `⟪v, Uⁿ v⟫ = ∫ e(nα) dσ_v(α)`   for all `n : ℤ`.

## Why this file is phrased as a predicate

The blueprint flags the *existence* of `σ_v` — the Herglotz theorem for positive definite
sequences on `ℤ` — as the largest piece of analysis infrastructure this project needs, and
recommends isolating it so that the rest of the development depends only on the defining
property.  That is what is done here: `HasSpectralMeasure U v σ` records the defining property,
and everything downstream (the quadratic form identity, Wiener's lemma, and in due course
`lem:atomless` and `cor:uniform-ergodic`) is proved *from* it.  Existence can then be supplied
separately without touching any of those proofs.

Mathlib has neither Herglotz nor the weak-* compactness of finite measures that the classical
Fejér-kernel proof uses.  It does have the Riesz–Markov–Kakutani theorem
(`RealRMK.integral_rieszMeasure`) and the continuous functional calculus for star-normal
elements, which together give a viable route; see the blueprint for the options.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Complex

/-- The circle `𝕋 = ℝ/ℤ`, on which spectral measures live. -/
abbrev Torus := AddCircle (1 : ℝ)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Definition `def:spectral-measure`.**  `σ` is a spectral measure for the unitary `U` at
the vector `v`: a finite positive Borel measure on `𝕋` whose Fourier coefficients are the
correlations `⟪v, Uⁿ v⟫`. -/
structure HasSpectralMeasure (U : H ≃ₗᵢ[ℂ] H) (v : H) (σ : Measure Torus) : Prop where
  /-- `σ` is finite. -/
  isFinite : IsFiniteMeasure σ
  /-- The defining property. -/
  inner_eq : ∀ n : ℤ, (inner ℂ v ((U ^ n) v) : ℂ) = ∫ α, fourier n α ∂σ

namespace HasSpectralMeasure

variable {U : H ≃ₗᵢ[ℂ] H} {v : H} {σ : Measure Torus}

/-- The total mass of a spectral measure is `‖v‖²`. -/
theorem measure_univ_eq (h : HasSpectralMeasure U v σ) :
    (σ Set.univ).toReal = ‖v‖ ^ 2 := by
  have := h.isFinite
  have h0 := h.inner_eq 0
  simp only [zpow_zero, LinearIsometryEquiv.coe_one, id_eq] at h0
  have hint : ∫ α, fourier (0 : ℤ) α ∂σ = ((σ Set.univ).toReal : ℂ) := by
    simp [Measure.real]
  rw [hint] at h0
  have hvv : (inner ℂ v v : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hvv] at h0
  exact_mod_cast h0.symm

/-- The correlations are the Fourier coefficients of `σ`, in the shifted form the expansion
below needs: `⟪U^a v, U^b v⟫ = ∫ e((b-a)α) dσ`. -/
theorem inner_zpow (h : HasSpectralMeasure U v σ) (a b : ℤ) :
    (inner ℂ ((U ^ a) v) ((U ^ b) v) : ℂ) = ∫ α, fourier (b - a) α ∂σ := by
  rw [← h.inner_eq (b - a)]
  have hb : (U ^ b) v = (U ^ a) ((U ^ (b - a)) v) := by
    have : U ^ b = (U ^ a) * (U ^ (b - a)) := by
      rw [← zpow_add U a (b - a)]
      congr 1
      ring
    rw [this]
    rfl
  rw [hb, LinearIsometryEquiv.inner_map_map]

/-- **The quadratic form identity.**  For a finite family of coefficients `a` and exponents
`k`,

  `‖∑ a i • U^(k i) v‖² = ∫ |∑ a i e(k i α)|² dσ`.

This is the form in which the spectral measure is used throughout: with `a` the constants of an
average and `k i = s·k_n`, the left side is the `L²` norm of an ergodic average and the right
side is the exponential sum estimate of `lem:irrational`. -/
theorem norm_sum_sq (h : HasSpectralMeasure U v σ) {ι : Type*} (F : Finset ι)
    (a : ι → ℂ) (k : ι → ℤ) :
    ‖∑ i ∈ F, a i • (U ^ (k i)) v‖ ^ 2
      = ∫ α, ‖∑ i ∈ F, a i * fourier (k i) α‖ ^ 2 ∂σ := by
  have := h.isFinite
  set X : H := ∑ i ∈ F, a i • (U ^ (k i)) v with hX
  set g : Torus → ℂ := fun α => ∑ i ∈ F, a i * fourier (k i) α with hg
  -- Every `fourier n` is integrable: it is continuous of modulus one and `σ` is finite.
  have hfint : ∀ n : ℤ, Integrable (fun α : Torus => fourier n α) σ := by
    intro n
    refine MemLp.integrable (q := ⊤) le_top ?_
    refine memLp_top_of_bound (fourier n).continuous.aestronglyMeasurable 1 ?_
    filter_upwards with α
    rw [fourier_apply]
    exact le_of_eq (Circle.norm_coe _)
  -- Expand the inner product into a double sum.
  have expand : (inner ℂ X X : ℂ)
      = ∑ i ∈ F, ∑ j ∈ F, (starRingEnd ℂ) (a i) * a j
          * (inner ℂ ((U ^ (k i)) v) ((U ^ (k j)) v) : ℂ) := by
    rw [hX, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right]
    ring
  -- Each inner product is a Fourier coefficient.
  have hpoint : ∀ α : Torus, ∑ i ∈ F, ∑ j ∈ F, (starRingEnd ℂ) (a i) * a j
      * fourier (k j - k i) α = (starRingEnd ℂ) (g α) * g α := by
    intro α
    have hconj : (starRingEnd ℂ) (g α) * g α
        = ∑ i ∈ F, ∑ j ∈ F,
            ((starRingEnd ℂ) (a i) * (starRingEnd ℂ) (fourier (k i) α))
              * (a j * fourier (k j) α) := by
      rw [hg]
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hconj]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sub_eq_add_neg, fourier_add, fourier_neg]
    ring
  -- Put the pieces together, interchanging the finite sums with the integral.
  have hcomplex : (inner ℂ X X : ℂ) = ∫ α, (starRingEnd ℂ) (g α) * g α ∂σ := by
    rw [expand]
    have hterm : ∀ i ∈ F, ∀ j ∈ F,
        (starRingEnd ℂ) (a i) * a j * (inner ℂ ((U ^ (k i)) v) ((U ^ (k j)) v) : ℂ)
          = ∫ α, (starRingEnd ℂ) (a i) * a j * fourier (k j - k i) α ∂σ := by
      intro i _ j _
      rw [h.inner_zpow, integral_const_mul]
    rw [Finset.sum_congr rfl fun i hi =>
      Finset.sum_congr rfl fun j hj => hterm i hi j hj]
    have hinner : ∀ i ∈ F, ∑ j ∈ F, ∫ α, (starRingEnd ℂ) (a i) * a j * fourier (k j - k i) α ∂σ
        = ∫ α, ∑ j ∈ F, (starRingEnd ℂ) (a i) * a j * fourier (k j - k i) α ∂σ := by
      intro i _
      rw [← integral_finsetSum]
      intro j _
      exact (hfint (k j - k i)).const_mul _
    rw [Finset.sum_congr rfl hinner, ← integral_finsetSum]
    · exact integral_congr_ae (by filter_upwards with α using hpoint α)
    · intro i _
      refine integrable_finsetSum _ fun j _ => ?_
      exact (hfint (k j - k i)).const_mul _
  -- Convert the complex identity into the real one.
  have hXnorm : (inner ℂ X X : ℂ) = ((‖X‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hgnorm : ∀ α : Torus, (starRingEnd ℂ) (g α) * g α = ((‖g α‖ ^ 2 : ℝ) : ℂ) := by
    intro α
    have := Complex.mul_conj (g α)
    rw [mul_comm] at this
    rw [this, Complex.normSq_eq_norm_sq]
  rw [hXnorm] at hcomplex
  rw [show (fun α => (starRingEnd ℂ) (g α) * g α) = fun α => ((‖g α‖ ^ 2 : ℝ) : ℂ) from
    funext hgnorm, integral_complex_ofReal] at hcomplex
  exact_mod_cast hcomplex

end HasSpectralMeasure

/-! ### Wiener's lemma

`lem:wiener`: the Cesàro means of `|σ̂(n)|²` converge to the sum of the squares of the atoms
of `σ`.  The proof is the standard one: write `|σ̂(n)|²` as a double integral against `σ × σ`,
average in `n`, and apply dominated convergence to

  `E_{1 ≤ n ≤ N} e(n(α-β)) → 1` if `α = β` and `→ 0` otherwise,

so that the limit is `(σ × σ)` of the diagonal, which is `∑_θ σ({θ})²`.
-/

/-- The Cesàro means of the characters, the kernel of Wiener's lemma. -/
noncomputable def cesaroChar (N : ℕ) (t : Torus) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, fourier (n : ℤ) t

theorem continuous_cesaroChar (N : ℕ) : Continuous (cesaroChar N) := by
  refine continuous_const.mul ?_
  exact continuous_finsetSum _ fun n _ => (fourier (n : ℤ)).continuous

theorem norm_cesaroChar_le_one {N : ℕ} (hN : 0 < N) (t : Torus) : ‖cesaroChar N t‖ ≤ 1 := by
  rw [cesaroChar, norm_mul, norm_inv]
  have hsum : ‖∑ n ∈ Finset.Icc 1 N, fourier (n : ℤ) t‖ ≤ (N : ℝ) := by
    calc ‖∑ n ∈ Finset.Icc 1 N, fourier (n : ℤ) t‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖fourier (n : ℤ) t‖ := norm_sum_le _ _
      _ = (N : ℝ) := by
          have hone : ∀ n ∈ Finset.Icc 1 N, ‖fourier (n : ℤ) t‖ = 1 := by
            intro n _
            rw [fourier_apply]
            exact Circle.norm_coe _
          rw [Finset.sum_congr rfl hone, Finset.sum_const, Nat.card_Icc]
          simp
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [Complex.norm_natCast]
  rw [inv_mul_le_iff₀ hNR]
  simpa using hsum

/-- The bound holds for every `N`, including `N = 0`, where the mean is `0`. -/
theorem norm_cesaroChar_le_one' (N : ℕ) (t : Torus) : ‖cesaroChar N t‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cesaroChar]
  · exact norm_cesaroChar_le_one hN t

/-- At `t = 0` every character is `1`, so the Cesàro mean is `1`. -/
@[simp] theorem cesaroChar_zero {N : ℕ} (hN : 0 < N) : cesaroChar N (0 : Torus) = 1 := by
  rw [cesaroChar]
  have : ∀ n ∈ Finset.Icc 1 N, fourier (n : ℤ) (0 : Torus) = 1 := by
    intro n _
    simp
  rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.card_Icc]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hN.ne')

/-- The characters are powers of the first one. -/
theorem fourier_eq_pow (n : ℕ) (t : Torus) : fourier (n : ℤ) t = (fourier 1 t) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [this, fourier_add, ih, pow_succ]

/-- Characters at integer frequencies are integer powers of the first character. -/
theorem fourier_eq_zpow (n : ℤ) (t : Torus) : fourier n t = (fourier 1 t) ^ n := by
  have hne : fourier 1 t ≠ 0 := by
    intro h
    have : ‖fourier (1 : ℤ) t‖ = 1 := by
      rw [fourier_apply]
      exact Circle.norm_coe _
    rw [h] at this
    simp at this
  induction n using Int.induction_on with
  | zero => simp
  | succ m ih =>
    rw [fourier_add, ih, zpow_add_one₀ hne]
  | pred m ih =>
    rw [show (-(m : ℤ) - 1) = (-(m : ℤ)) + (-1) by ring, fourier_add, ih,
      zpow_add₀ hne, zpow_neg_one]
    congr 1
    have hnorm : ‖fourier (1 : ℤ) t‖ = 1 := by
      rw [fourier_apply]; exact Circle.norm_coe _
    rw [show ((-1 : ℤ)) = -(1 : ℤ) from rfl, fourier_neg, eq_comm, inv_eq_iff_eq_inv,
      Complex.inv_def, Complex.normSq_eq_norm_sq, RCLike.norm_conj, hnorm]
    simp

/-- Away from `0`, the Cesàro means of the characters tend to `0`: the geometric sum is
bounded while the normalisation grows. -/
theorem tendsto_cesaroChar_of_ne_zero {t : Torus} (ht : t ≠ 0) :
    Filter.Tendsto (fun N => cesaroChar N t) Filter.atTop (nhds 0) := by
  set z : ℂ := fourier 1 t with hz
  have hz1 : z ≠ 1 := by
    rw [hz, fourier_one]
    intro hcon
    refine ht ?_
    have : (AddCircle.toCircle t : ℂ) = (AddCircle.toCircle (0 : Torus) : ℂ) := by
      rw [hcon]
      simp
    exact AddCircle.injective_toCircle one_ne_zero (Circle.coe_injective this)
  -- The geometric sums are bounded.
  have hgeom : ∀ N : ℕ, ‖∑ n ∈ Finset.Icc 1 N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
    intro N
    have hsum : ∑ n ∈ Finset.Icc 1 N, z ^ n = (z ^ (N + 1) - z) / (z - 1) := by
      have h := geom_sum_eq hz1 (N + 1)
      have h0 : ∑ n ∈ Finset.range (N + 1), z ^ n = 1 + ∑ n ∈ Finset.Icc 1 N, z ^ n := by
        have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
          ext n
          simp only [Finset.mem_Icc, Finset.mem_Ico]
          omega
        rw [hIcc, Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel]
        rw [Finset.sum_range_succ']
        simp [add_comm]
      rw [h0] at h
      field_simp at h ⊢
      linear_combination h
    rw [hsum, norm_div]
    have hznorm : ‖z‖ = 1 := by
      rw [hz, fourier_apply]
      exact Circle.norm_coe _
    have hnum : ‖z ^ (N + 1) - z‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, hznorm]
      norm_num
    have hden : (0 : ℝ) < ‖z - 1‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.2 hz1
    exact div_le_div_of_nonneg_right hnum hden.le |>.trans_eq rfl
  -- So the Cesàro means vanish.
  have hbound : ∀ N : ℕ, 0 < N → ‖cesaroChar N t‖ ≤ (2 / ‖z - 1‖) / N := by
    intro N hN
    rw [cesaroChar, norm_mul, norm_inv, Complex.norm_natCast]
    have := hgeom N
    rw [Finset.sum_congr rfl fun n _ => fourier_eq_pow n t] at *
    rw [inv_mul_eq_div, div_le_div_iff_of_pos_right (by exact_mod_cast hN)]
    exact this
  refine squeeze_zero_norm' (a := fun N : ℕ => (2 / ‖z - 1‖) / N)
    (by filter_upwards [Filter.eventually_gt_atTop 0] with N hN using hbound N hN)
    (tendsto_const_div_atTop_nhds_zero_nat _)

/-! ### The `range`-indexed kernel

`birkhoffAverage` averages over `Finset.range N`, so the `Icc 1 N` kernel above needs a
companion.  The two differ by at most `2/N`, which is enough to transport the limits. -/

/-- The Cesàro mean of the characters over `range N`, matching `birkhoffAverage`. -/
noncomputable def cesaroChar' (N : ℕ) (t : Torus) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, fourier (n : ℤ) t

theorem norm_cesaroChar'_le_one (N : ℕ) (t : Torus) : ‖cesaroChar' N t‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cesaroChar']
  rw [cesaroChar', norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ n ∈ Finset.range N, fourier (n : ℤ) t‖ ≤ (N : ℝ) := by
    calc ‖∑ n ∈ Finset.range N, fourier (n : ℤ) t‖
        ≤ ∑ n ∈ Finset.range N, ‖fourier (n : ℤ) t‖ := norm_sum_le _ _
      _ = (N : ℝ) := by
          have hone : ∀ n ∈ Finset.range N, ‖fourier (n : ℤ) t‖ = 1 := by
            intro n _
            rw [fourier_apply]
            exact Circle.norm_coe _
          rw [Finset.sum_congr rfl hone]
          simp
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [inv_mul_le_iff₀ hNR]
  simpa using hsum

@[simp] theorem cesaroChar'_zero {N : ℕ} (hN : 0 < N) : cesaroChar' N (0 : Torus) = 1 := by
  rw [cesaroChar']
  have hone : ∀ n ∈ Finset.range N, fourier (n : ℤ) (0 : Torus) = 1 := by
    intro n _
    simp
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hN.ne')

/-- The two kernels differ by at most `2/N`: their index sets differ only at `0` and `N`. -/
theorem norm_cesaroChar'_sub_le (N : ℕ) (t : Torus) :
    ‖cesaroChar' N t - cesaroChar N t‖ ≤ 2 / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cesaroChar', cesaroChar]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : ∑ n ∈ Finset.range N, fourier (n : ℤ) t
      = fourier (0 : ℤ) t + ∑ n ∈ Finset.Icc 1 (N - 1), fourier (n : ℤ) t := by
    have hset : Finset.range N = insert 0 (Finset.Icc 1 (N - 1)) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    norm_num
  have hsplit2 : ∑ n ∈ Finset.Icc 1 N, fourier (n : ℤ) t
      = (∑ n ∈ Finset.Icc 1 (N - 1), fourier (n : ℤ) t) + fourier (N : ℤ) t := by
    have hset : Finset.Icc 1 N = insert N (Finset.Icc 1 (N - 1)) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp; omega), add_comm]
  rw [cesaroChar', cesaroChar, hsplit, hsplit2, ← mul_sub]
  have harith : (fourier (0 : ℤ) t + ∑ n ∈ Finset.Icc 1 (N - 1), fourier (n : ℤ) t)
      - ((∑ n ∈ Finset.Icc 1 (N - 1), fourier (n : ℤ) t) + fourier (N : ℤ) t)
      = fourier (0 : ℤ) t - fourier (N : ℤ) t := by ring
  rw [harith, norm_mul, norm_inv, Complex.norm_natCast]
  have hnum : ‖fourier (0 : ℤ) t - fourier (N : ℤ) t‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have h0 : ‖fourier (0 : ℤ) t‖ = 1 := by rw [fourier_apply]; exact Circle.norm_coe _
    have hN' : ‖fourier (N : ℤ) t‖ = 1 := by rw [fourier_apply]; exact Circle.norm_coe _
    rw [h0, hN']
    norm_num
  rw [inv_mul_le_iff₀ hNR]
  calc ‖fourier (0 : ℤ) t - fourier (N : ℤ) t‖ ≤ 2 := hnum
    _ = (N : ℝ) * (2 / (N : ℝ)) := by field_simp

/-! ### Wiener's lemma proper

`|σ̂(n)|²` is a double integral against `σ × σ`; averaging in `n` turns the integrand into the
Cesàro kernel at `α - β`, which tends to the indicator of the diagonal.
-/

/-- The Fourier coefficient of a measure on the torus. -/
noncomputable def sigmaHat (σ : Measure Torus) (n : ℤ) : ℂ := ∫ α, fourier n α ∂σ

variable {σ : Measure Torus} [IsFiniteMeasure σ]

theorem integrable_fourier (n : ℤ) : Integrable (fun α : Torus => fourier n α) σ := by
  refine MemLp.integrable (q := ⊤) le_top ?_
  refine memLp_top_of_bound (fourier n).continuous.aestronglyMeasurable 1 ?_
  filter_upwards with α
  rw [fourier_apply]
  exact le_of_eq (Circle.norm_coe _)

/-- `|σ̂(n)|²` as a double integral: the integrand is `e(n(α-β))`. -/
theorem sq_norm_sigmaHat (n : ℤ) :
    ((‖sigmaHat σ n‖ ^ 2 : ℝ) : ℂ)
      = ∫ p : Torus × Torus, fourier n (p.1 - p.2) ∂(σ.prod σ) := by
  have hmul : ∀ p : Torus × Torus,
      fourier n (p.1 - p.2) = fourier n p.1 * (starRingEnd ℂ) (fourier n p.2) := by
    intro p
    have hneg : (AddCircle.toCircle (-(n • p.2)) : ℂ)
        = (starRingEnd ℂ) (fourier n p.2) := by
      rw [fourier_apply]
      exact fourier_neg' (T := (1 : ℝ))
    rw [fourier_apply, fourier_apply, smul_sub, sub_eq_add_neg, AddCircle.toCircle_add]
    push_cast
    rw [hneg, fourier_apply]
  rw [integral_congr_ae (Filter.Eventually.of_forall hmul)]
  rw [integral_prod_mul (f := fun α => fourier n α)
    (g := fun β => (starRingEnd ℂ) (fourier n β))]
  rw [integral_conj]
  change _ = sigmaHat σ n * (starRingEnd ℂ) (sigmaHat σ n)
  rw [mul_comm]
  have := Complex.mul_conj (sigmaHat σ n)
  rw [mul_comm] at this
  rw [this, Complex.normSq_eq_norm_sq]

/-- Averaging the double integrals turns the integrand into the Cesàro kernel. -/
theorem cesaro_sq_norm_sigmaHat {N : ℕ} (_hN : 0 < N) :
    (((N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ‖sigmaHat σ (n : ℤ)‖ ^ 2 : ℝ) : ℂ)
      = ∫ p : Torus × Torus, cesaroChar N (p.1 - p.2) ∂(σ.prod σ) := by
  have hint : ∀ n : ℤ, Integrable
      (fun p : Torus × Torus => fourier n (p.1 - p.2)) (σ.prod σ) := by
    intro n
    refine MemLp.integrable (q := ⊤) le_top ?_
    refine memLp_top_of_bound ?_ 1 ?_
    · exact ((fourier n).continuous.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
    · filter_upwards with p
      rw [fourier_apply]
      exact le_of_eq (Circle.norm_coe _)
  have hswap : (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
        (∫ p : Torus × Torus, fourier (n : ℤ) (p.1 - p.2) ∂(σ.prod σ))
      = ∫ p : Torus × Torus, cesaroChar N (p.1 - p.2) ∂(σ.prod σ) := by
    rw [← integral_finsetSum (Finset.Icc 1 N) fun n _ => hint (n : ℤ), ← integral_const_mul]
    rfl
  rw [← hswap, Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  · norm_num
  · exact Finset.sum_congr rfl fun n _ => sq_norm_sigmaHat (σ := σ) (n : ℤ)

/-- The Cesàro kernel at `p.1 - p.2` tends to the indicator of the diagonal. -/
theorem tendsto_cesaroChar_sub (p : Torus × Torus) :
    Filter.Tendsto (fun N => cesaroChar N (p.1 - p.2)) Filter.atTop
      (nhds (Set.indicator {q : Torus × Torus | q.1 = q.2} (fun _ => (1 : ℂ)) p)) := by
  by_cases h : p.1 = p.2
  · have hz : p.1 - p.2 = 0 := by rw [h]; simp
    rw [hz, Set.indicator_of_mem (show p ∈ {q : Torus × Torus | q.1 = q.2} from h)]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    exact (cesaroChar_zero hN).symm
  · have hz : p.1 - p.2 ≠ 0 := sub_ne_zero.2 h
    rw [Set.indicator_of_notMem (show p ∉ {q : Torus × Torus | q.1 = q.2} from h)]
    exact tendsto_cesaroChar_of_ne_zero hz

/-- **Wiener's lemma (`lem:wiener`).**  The Cesàro means of `|σ̂(n)|²` converge to the measure
of the diagonal under `σ × σ`. -/
theorem tendsto_cesaro_sq_norm_sigmaHat :
    Filter.Tendsto
      (fun N : ℕ => ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ‖sigmaHat σ (n : ℤ)‖ ^ 2 : ℝ))
      Filter.atTop
      (nhds ((σ.prod σ) {q : Torus × Torus | q.1 = q.2}).toReal) := by
  -- Dominated convergence for the complex integrals.
  have hcont : ∀ N : ℕ, Continuous (fun p : Torus × Torus => cesaroChar N (p.1 - p.2)) :=
    fun N => (continuous_cesaroChar N).comp (continuous_fst.sub continuous_snd)
  have hmeas : ∀ N : ℕ, AEStronglyMeasurable
      (fun p : Torus × Torus => cesaroChar N (p.1 - p.2)) (σ.prod σ) :=
    fun N => (hcont N).aestronglyMeasurable
  have hdiag : MeasurableSet {q : Torus × Torus | q.1 = q.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun (N : ℕ) (p : Torus × Torus) => cesaroChar N (p.1 - p.2))
    (f := Set.indicator {q : Torus × Torus | q.1 = q.2} (fun _ => (1 : ℂ)))
    (bound := fun _ => (1 : ℝ)) hmeas
    (integrable_const 1)
    (fun N => Filter.Eventually.of_forall fun p => norm_cesaroChar_le_one' N _)
    (Filter.Eventually.of_forall fun p => tendsto_cesaroChar_sub p)
  -- The limit is the measure of the diagonal.
  have hlim : (∫ p : Torus × Torus,
        Set.indicator {q : Torus × Torus | q.1 = q.2} (fun _ => (1 : ℂ)) p ∂(σ.prod σ))
      = ((((σ.prod σ) {q : Torus × Torus | q.1 = q.2}).toReal : ℝ) : ℂ) := by
    rw [integral_indicator_const _ hdiag]
    simp [Measure.real]
  rw [hlim] at hdct
  -- Take real parts: the integrals are the (real) Cesàro means.
  have hre := (Complex.continuous_re.tendsto _).comp hdct
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  refine hre.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  rw [← cesaro_sq_norm_sigmaHat hN, Complex.ofReal_re]

/-- A single atom contributes `σ({θ})²` to the diagonal. -/
theorem sq_measure_singleton_le_diagonal (θ : Torus) :
    (σ {θ}).toReal ^ 2 ≤ ((σ.prod σ) {q : Torus × Torus | q.1 = q.2}).toReal := by
  have hsub : ({θ} : Set Torus) ×ˢ ({θ} : Set Torus)
      ⊆ {q : Torus × Torus | q.1 = q.2} := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    simp only [Set.mem_singleton_iff] at ha hb
    simp [ha, hb]
  have hprod : (σ.prod σ) (({θ} : Set Torus) ×ˢ ({θ} : Set Torus)) = σ {θ} * σ {θ} :=
    Measure.prod_prod _ _
  have hle := measure_mono (μ := σ.prod σ) hsub
  rw [hprod] at hle
  have hfin : σ {θ} ≠ ⊤ := measure_ne_top _ _
  calc (σ {θ}).toReal ^ 2 = ((σ {θ} * σ {θ}).toReal) := by
        rw [ENNReal.toReal_mul]; ring
    _ ≤ ((σ.prod σ) {q : Torus × Torus | q.1 = q.2}).toReal := by
        refine ENNReal.toReal_mono (measure_ne_top _ _) hle

/-- **Wiener's lemma, the form used in `lem:atomless`.**  If the Cesàro means of `|σ̂(n)|²`
vanish then `σ` has no atoms. -/
theorem noAtoms_of_tendsto_cesaro_zero
    (h : Filter.Tendsto
      (fun N : ℕ => ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ‖sigmaHat σ (n : ℤ)‖ ^ 2 : ℝ))
      Filter.atTop (nhds 0)) :
    ∀ θ : Torus, σ {θ} = 0 := by
  intro θ
  have hdiag : ((σ.prod σ) {q : Torus × Torus | q.1 = q.2}).toReal = 0 :=
    tendsto_nhds_unique tendsto_cesaro_sq_norm_sigmaHat h
  have hle := sq_measure_singleton_le_diagonal (σ := σ) θ
  rw [hdiag] at hle
  have hzero : (σ {θ}).toReal = 0 := by nlinarith [sq_nonneg ((σ {θ}).toReal)]
  exact (ENNReal.toReal_eq_zero_iff _).1 hzero |>.resolve_right (measure_ne_top _ _)

/-! ### The converse: a non-vanishing Cesàro mean forces an atom

This is the entry point of the Furstenberg dichotomy (`lem:dichotomy`).  Note that it does
**not** need the full identity `(σ × σ)(Δ) = ∑_θ σ({θ})²`: by Fubini the diagonal's measure is
`∫⁻ σ({α}) dσ(α)`, and an integral of a non-negative function is zero as soon as the function
vanishes identically.  So positivity of the diagonal directly exhibits an atom.
-/

/-- The measure of the diagonal is the integral of the atom sizes. -/
theorem prod_diagonal_eq_lintegral :
    (σ.prod σ) {q : Torus × Torus | q.1 = q.2} = ∫⁻ α, σ {α} ∂σ := by
  rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
  congr 1
  funext α
  congr 1
  ext β
  simp [eq_comm]

/-- If the diagonal has positive measure then `σ` has an atom. -/
theorem exists_atom_of_diagonal_ne_zero
    (h : (σ.prod σ) {q : Torus × Torus | q.1 = q.2} ≠ 0) : ∃ θ : Torus, σ {θ} ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine h ?_
  rw [prod_diagonal_eq_lintegral]
  have hzero : (fun α => σ {α}) = fun _ => 0 := funext fun α => hcon α
  rw [hzero]
  simp

/-- **The converse of Wiener's lemma.**  If the Cesàro means of `|σ̂(n)|²` do not vanish then
`σ` has an atom. -/
theorem exists_atom_of_not_tendsto_cesaro_zero
    (h : ¬ Filter.Tendsto
      (fun N : ℕ => ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ‖sigmaHat σ (n : ℤ)‖ ^ 2 : ℝ))
      Filter.atTop (nhds 0)) :
    ∃ θ : Torus, σ {θ} ≠ 0 := by
  refine exists_atom_of_diagonal_ne_zero ?_
  intro hzero
  refine h ?_
  have := tendsto_cesaro_sq_norm_sigmaHat (σ := σ)
  rwa [hzero, ENNReal.toReal_zero] at this

/-! ### Eigenfunctions from atoms

The entry point of the Hilbert–Schmidt step of `lem:dichotomy`: an atom of the spectral
measure at `θ` produces a genuine eigenvector of `U` with eigenvalue `e(θ)`.

The two ingredients are Mathlib's von Neumann mean ergodic theorem, applied to the
contraction `e(-θ) • U`, and the quadratic form identity `norm_sum_sq`, which turns the norm
of a Birkhoff average into `∫ |cesaroChar' N (α - θ)|² dσ` and hence, by dominated
convergence, into `σ({θ})`.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace HasSpectralMeasure

variable {U : H ≃ₗᵢ[ℂ] H} {v : H} {σ : Measure Torus}

/-- The Birkhoff averages of `e(-θ) • U` at `v` have squared norm tending to `σ({θ})`. -/
theorem tendsto_norm_birkhoff_sq (h : HasSpectralMeasure U v σ) (θ : Torus) :
    Filter.Tendsto
      (fun N : ℕ => ‖∑ n ∈ Finset.range N,
        ((N : ℂ)⁻¹ * (starRingEnd ℂ) (fourier (n : ℤ) θ)) • (U ^ (n : ℤ)) v‖ ^ 2)
      Filter.atTop (nhds ((σ {θ}).toReal)) := by
  have := h.isFinite
  -- The quadratic form identity turns each norm into an integral of the kernel.
  have hnorm : ∀ N : ℕ, ‖∑ n ∈ Finset.range N,
      ((N : ℂ)⁻¹ * (starRingEnd ℂ) (fourier (n : ℤ) θ)) • (U ^ (n : ℤ)) v‖ ^ 2
      = ∫ α, ‖cesaroChar' N (α - θ)‖ ^ 2 ∂σ := by
    intro N
    rw [h.norm_sum_sq (Finset.range N)
      (fun n => (N : ℂ)⁻¹ * (starRingEnd ℂ) (fourier (n : ℤ) θ)) (fun n => (n : ℤ))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
    have hinner : ∑ n ∈ Finset.range N,
        ((N : ℂ)⁻¹ * (starRingEnd ℂ) (fourier (n : ℤ) θ)) * fourier (n : ℤ) α
        = cesaroChar' N (α - θ) := by
      rw [cesaroChar', Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hchar : fourier (n : ℤ) (α - θ)
          = fourier (n : ℤ) α * (starRingEnd ℂ) (fourier (n : ℤ) θ) := by
        have hneg : (AddCircle.toCircle (-((n : ℤ) • θ)) : ℂ)
            = (starRingEnd ℂ) (fourier (n : ℤ) θ) := by
          rw [fourier_apply]
          exact fourier_neg' (T := (1 : ℝ))
        rw [fourier_apply, fourier_apply, smul_sub, sub_eq_add_neg, AddCircle.toCircle_add]
        push_cast
        rw [hneg, fourier_apply]
      rw [hchar]
      ring
    simp only []
    rw [hinner]
  -- Dominated convergence: the kernel tends to the indicator of `{θ}`.
  have hcont : ∀ N : ℕ, Continuous fun α : Torus => cesaroChar' N (α - θ) := by
    intro N
    have hk : Continuous (cesaroChar' N) :=
      continuous_const.mul (continuous_finsetSum _ fun n _ => (fourier (n : ℤ)).continuous)
    exact hk.comp (continuous_id.sub continuous_const)
  have hptw : ∀ α : Torus, Filter.Tendsto (fun N => ‖cesaroChar' N (α - θ)‖ ^ 2)
      Filter.atTop (nhds (Set.indicator {θ} (fun _ => (1 : ℝ)) α)) := by
    intro α
    by_cases hα : α = θ
    · subst hα
      rw [Set.indicator_of_mem (by simp : α ∈ ({α} : Set Torus))]
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_gt_atTop 0] with N hN
      rw [show α - α = (0 : Torus) by simp, cesaroChar'_zero hN]
      simp
    · rw [Set.indicator_of_notMem (by simpa using hα)]
      have hne : α - θ ≠ 0 := sub_ne_zero.2 hα
      have hdiff : Filter.Tendsto (fun N => cesaroChar' N (α - θ)) Filter.atTop (nhds 0) := by
        have hIcc := tendsto_cesaroChar_of_ne_zero hne
        have hsmall : Filter.Tendsto
            (fun N : ℕ => cesaroChar' N (α - θ) - cesaroChar N (α - θ))
            Filter.atTop (nhds 0) := by
          refine squeeze_zero_norm' (a := fun N : ℕ => 2 / (N : ℝ))
            (Filter.Eventually.of_forall fun N => norm_cesaroChar'_sub_le N (α - θ))
            (tendsto_const_div_atTop_nhds_zero_nat 2)
        simpa using hsmall.add hIcc
      have := (continuous_pow 2).continuousAt.tendsto.comp
        ((continuous_norm.tendsto 0).comp hdiff)
      simpa [Function.comp_def] using this
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun (N : ℕ) (α : Torus) => ‖cesaroChar' N (α - θ)‖ ^ 2)
    (f := Set.indicator {θ} (fun _ => (1 : ℝ)))
    (bound := fun _ => (1 : ℝ))
    (fun N => ((hcont N).norm.pow 2).aestronglyMeasurable)
    (integrable_const (μ := σ) 1)
    (fun N => Filter.Eventually.of_forall fun α => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have := norm_cesaroChar'_le_one N (α - θ)
      nlinarith [norm_nonneg (cesaroChar' N (α - θ))])
    (Filter.Eventually.of_forall hptw)
  rw [integral_indicator_const _ (measurableSet_singleton θ)] at hdct
  simp only [smul_eq_mul, mul_one, Measure.real] at hdct
  exact (Filter.Tendsto.congr (fun N => (hnorm N).symm) hdct)

/-- **Eigenfunction from an atom.**  If the spectral measure of `U` at `v` has an atom at `θ`,
then `U` has an eigenvector with eigenvalue `e(θ)`.

This is the entry point of the Hilbert–Schmidt step of `lem:dichotomy`.  Von Neumann's mean
ergodic theorem makes the Birkhoff averages of the contraction `e(-θ) • U` converge to the
orthogonal projection onto its fixed points, and `tendsto_norm_birkhoff_sq` shows that the
limit has squared norm `σ({θ}) ≠ 0`, so it is a non-zero fixed point. -/
theorem exists_eigenvector_of_atom [CompleteSpace H] (h : HasSpectralMeasure U v σ)
    {θ : Torus} (hθ : σ {θ} ≠ 0) :
    ∃ w : H, w ≠ 0 ∧ U w = fourier 1 θ • w := by
  classical
  have hfin := h.isFinite
  set c : ℂ := (starRingEnd ℂ) (fourier 1 θ) with hc
  have hcnorm : ‖c‖ = 1 := by
    rw [hc, RCLike.norm_conj, fourier_apply]
    exact Circle.norm_coe _
  -- The contraction `W = e(-θ) • U`.
  set W : H →L[ℂ] H := c • (U.toLinearIsometry.toContinuousLinearMap) with hW
  have hWnorm : ‖W‖ ≤ 1 := by
    rw [hW, norm_smul, hcnorm, one_mul]
    exact LinearIsometry.norm_toContinuousLinearMap_le U.toLinearIsometry
  -- Its Birkhoff averages are the sums appearing in `tendsto_norm_birkhoff_sq`.
  have hiter : ∀ (n : ℕ) (x : H), W^[n] x = (c ^ n) • (U ^ (n : ℤ)) x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, hW]
      simp only [smul_apply, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry, map_smul]
      have hUU : U ((U ^ (n : ℤ)) x) = (U ^ ((n + 1 : ℕ) : ℤ)) x := by
        rw [show (((n + 1 : ℕ)) : ℤ) = 1 + (n : ℤ) by push_cast; ring,
          zpow_add U 1 (n : ℤ), zpow_one]
        rfl
      rw [hUU, smul_smul, pow_succ, mul_comm (c ^ n) c]
  have hbirk : ∀ N : ℕ, birkhoffAverage ℂ W _root_.id N v
      = ∑ n ∈ Finset.range N, ((N : ℂ)⁻¹ * c ^ n) • (U ^ (n : ℤ)) v := by
    intro N
    rw [birkhoffAverage, birkhoffSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show _root_.id (W^[n] v) = W^[n] v from rfl, hiter n v, smul_smul]
  -- Mean ergodic theorem.
  set Psub := (W.eqLocus (1 : H →L[ℂ] H)).orthogonalProjectionOnto v with hPsub
  set w : H := (Psub : H) with hw
  have hme := W.tendsto_birkhoffAverage_orthogonalProjection hWnorm v
  -- The norms converge to `σ({θ}) ≠ 0`, so the limit is non-zero.
  have hcpow : ∀ n : ℕ, c ^ n = (starRingEnd ℂ) (fourier (n : ℤ) θ) := by
    intro n
    rw [hc, ← map_pow]
    congr 1
    rw [fourier_eq_zpow (n : ℤ) θ, zpow_natCast]
  have hnormlim := h.tendsto_norm_birkhoff_sq θ
  have hnormlim' : Filter.Tendsto (fun N : ℕ => ‖birkhoffAverage ℂ W _root_.id N v‖ ^ 2)
      Filter.atTop (nhds ((σ {θ}).toReal)) := by
    refine hnormlim.congr fun N => ?_
    rw [hbirk N]
    congr 2
    exact Finset.sum_congr rfl fun n _ => by rw [hcpow n]
  have hlim : Filter.Tendsto (fun N : ℕ => ‖birkhoffAverage ℂ W _root_.id N v‖ ^ 2)
      Filter.atTop (nhds (‖w‖ ^ 2)) :=
    ((continuous_pow 2).continuousAt.tendsto.comp ((continuous_norm.tendsto _).comp hme))
  have hwnorm : ‖w‖ ^ 2 = (σ {θ}).toReal := tendsto_nhds_unique hlim hnormlim'
  have hwne : w ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hwnorm
    refine hθ ?_
    have hz : (σ {θ}).toReal = 0 := by simpa using hwnorm.symm
    exact (ENNReal.toReal_eq_zero_iff _).1 hz |>.resolve_right (measure_ne_top _ _)
  -- A fixed point of `W` is an eigenvector of `U`.
  refine ⟨w, hwne, ?_⟩
  have hfix : c • U w = w := by
    have hmem : W w = w := Psub.2
    rw [hW] at hmem
    simpa using hmem
  have hcinv : (fourier 1 θ) * c = 1 := by
    rw [hc, mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      show ‖fourier (1 : ℤ) θ‖ = 1 by rw [fourier_apply]; exact Circle.norm_coe _]
    norm_num
  calc U w = (fourier 1 θ * c) • U w := by rw [hcinv, one_smul]
    _ = fourier 1 θ • (c • U w) := by rw [smul_smul]
    _ = fourier 1 θ • w := by rw [hfix]

end HasSpectralMeasure

end CantorSzemeredi

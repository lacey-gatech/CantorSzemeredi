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

end CantorSzemeredi

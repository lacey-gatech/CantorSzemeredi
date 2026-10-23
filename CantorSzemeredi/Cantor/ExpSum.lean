/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Cantor.Enum

/-!
# Exponential sums along a Cantor set

This file is Stage 2 of the blueprint (`blueprint/src/chapter/cantor.tex`, section
"A uniform exponential sum estimate").  The goal is Lemma `lem:irrational`: for every `β`
outside a countable exceptional set,

  `Φ_L β := ⨆ M, |E_{M ≤ n < M+L} e (β * k n)| → 0`  as  `L → ∞`.

The supremum over the starting index `M` is the point: it is what makes every average in the
project *uniform*, and hence what turns a positive density into a syndetic set of indices.

The Cantor-specific input is `enum_block` (`lem:diff`(ii)), which enters twice:

* `enum_expSum_pow`, the factorization of the sum over a full block `[0, δ^ℓ)` into a product
  of digit averages, and
* `windowSplit`, which splits an arbitrary window `[M, N)` into full blocks plus `O(δ^i)`
  leftover indices, *with a bound not depending on `M`*.
-/

namespace CantorSzemeredi

open Complex Finset

/-- `e θ = exp (2 π i θ)`. -/
noncomputable def e (θ : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * θ)

@[simp] theorem abs_e (θ : ℝ) : ‖e θ‖ = 1 := by
  rw [e, Complex.norm_exp]
  norm_num

theorem e_add (θ₁ θ₂ : ℝ) : e (θ₁ + θ₂) = e θ₁ * e θ₂ := by
  rw [e, e, e, ← Complex.exp_add]
  push_cast
  ring_nf

@[simp] theorem e_zero : e 0 = 1 := by simp [e]

/-- The exponential of an integer is `1`. -/
@[simp] theorem e_intCast (k : ℤ) : e (k : ℝ) = 1 := by
  rw [e, Complex.exp_eq_one_iff]
  exact ⟨k, by push_cast; ring⟩

/-- `e θ = 1` exactly on the integers. -/
theorem e_eq_one_iff {θ : ℝ} : e θ = 1 ↔ ∃ k : ℤ, θ = (k : ℝ) := by
  constructor
  · intro h
    rw [e, Complex.exp_eq_one_iff] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have hπ : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hc : ((θ : ℂ)) = ((k : ℤ) : ℂ) :=
      mul_left_cancel₀ hπ (by linear_combination hk)
    exact_mod_cast hc
  · rintro ⟨k, rfl⟩
    exact e_intCast k

/-- `e` is continuous. -/
theorem continuous_e : Continuous e := by
  unfold e
  fun_prop

/-! ### The distance to the nearest integer -/

/-- `‖θ‖`, the distance from `θ` to the nearest integer, written as a function of the
fractional part. -/
noncomputable def nrm (θ : ℝ) : ℝ := min (Int.fract θ) (1 - Int.fract θ)

theorem nrm_nonneg (θ : ℝ) : 0 ≤ nrm θ :=
  le_min (Int.fract_nonneg θ) (by linarith [Int.fract_lt_one θ])

theorem nrm_le_half (θ : ℝ) : nrm θ ≤ 1 / 2 := by
  have h1 := min_le_left (Int.fract θ) (1 - Int.fract θ)
  have h2 := min_le_right (Int.fract θ) (1 - Int.fract θ)
  unfold nrm
  linarith

/-- `‖θ‖ = 0` exactly on the integers. -/
theorem nrm_eq_zero_iff {θ : ℝ} : nrm θ = 0 ↔ ∃ k : ℤ, θ = (k : ℝ) := by
  constructor
  · intro h
    have hf : Int.fract θ = 0 := by
      rcases min_cases (Int.fract θ) (1 - Int.fract θ) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [nrm, he] at h; exact h
      · rw [nrm, he] at h; linarith [Int.fract_lt_one θ]
    refine ⟨⌊θ⌋, ?_⟩
    have : Int.fract θ = θ - (⌊θ⌋ : ℝ) := rfl
    rw [this] at hf
    linarith
  · rintro ⟨k, rfl⟩
    simp [nrm]

/-- If `θ` is at distance at least `η` from the integers, its fractional part lies in
`[η, 1 - η]`. -/
theorem fract_mem_Icc {θ η : ℝ} (h : η ≤ nrm θ) : Int.fract θ ∈ Set.Icc η (1 - η) := by
  refine ⟨h.trans (min_le_left _ _), ?_⟩
  have := h.trans (min_le_right (Int.fract θ) (1 - Int.fract θ))
  linarith

/-- **Expansion of small distances.**  If `θ` is closer than `1/(2n)` to the integers then
multiplying by `n` multiplies the distance by `n`. -/
theorem nrm_natCast_mul {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (h : nrm θ < 1 / (2 * n)) :
    nrm ((n : ℝ) * θ) = n * nrm θ := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hf0 : 0 ≤ Int.fract θ := Int.fract_nonneg θ
  have hf1 : Int.fract θ < 1 := Int.fract_lt_one θ
  have hkey : Int.fract ((n : ℝ) * θ) = Int.fract ((n : ℝ) * Int.fract θ) := by
    have hsplit : (n : ℝ) * θ = (((n * ⌊θ⌋ : ℤ) : ℝ)) + (n : ℝ) * Int.fract θ := by
      have : Int.fract θ = θ - (⌊θ⌋ : ℝ) := rfl
      rw [this]; push_cast; ring
    rw [hsplit, Int.fract_intCast_add]
  rcases le_total (Int.fract θ) (1 - Int.fract θ) with hc | hc
  · have hnrm : nrm θ = Int.fract θ := min_eq_left hc
    rw [hnrm] at h ⊢
    have hlt : (n : ℝ) * Int.fract θ < 1 / 2 := by
      calc (n : ℝ) * Int.fract θ < (n : ℝ) * (1 / (2 * n)) :=
            mul_lt_mul_of_pos_left h hnpos
        _ = 1 / 2 := by field_simp
    have hfr : Int.fract ((n : ℝ) * Int.fract θ) = (n : ℝ) * Int.fract θ :=
      Int.fract_eq_self.2 ⟨by positivity, by linarith⟩
    rw [nrm, hkey, hfr]
    exact min_eq_left (by linarith)
  · have hnrm : nrm θ = 1 - Int.fract θ := min_eq_right hc
    rw [hnrm] at h ⊢
    set v : ℝ := (n : ℝ) * (1 - Int.fract θ) with hv
    have hv0 : 0 < v := by rw [hv]; have : 0 < 1 - Int.fract θ := by linarith
                           positivity
    have hvlt : v < 1 / 2 := by
      calc v = (n : ℝ) * (1 - Int.fract θ) := hv
        _ < (n : ℝ) * (1 / (2 * n)) := mul_lt_mul_of_pos_left h hnpos
        _ = 1 / 2 := by field_simp
    have hfr : Int.fract ((n : ℝ) * Int.fract θ) = 1 - v := by
      have hrw : (n : ℝ) * Int.fract θ = (((n : ℤ) - 1 : ℤ) : ℝ) + (1 - v) := by
        rw [hv]; push_cast; ring
      rw [hrw, Int.fract_intCast_add, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
    rw [nrm, hkey, hfr]
    have hsimp : (1 : ℝ) - (1 - v) = v := by ring
    rw [hsimp]
    exact min_eq_right (by linarith)

/-! ### The equality case of the triangle inequality for sums of unit vectors -/

/-- If `n` unit vectors `e (f m)` have sum of modulus `n`, and the first of them is `1`, then
all of them are `1`.  This is the equality case of the triangle inequality, in the special
form needed for the digit average. -/
private theorem e_eq_one_of_norm_sum {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ) (h0 : e (f 0) = 1)
    (h : ‖∑ m ∈ range n, e (f m)‖ = (n : ℝ)) : ∀ m ∈ range n, e (f m) = 1 := by
  set S : ℂ := ∑ m ∈ range n, e (f m) with hSdef
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnC : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hSne : S ≠ 0 := by
    intro hz; rw [hz, norm_zero] at h; linarith
  set u : ℂ := (starRingEnd ℂ) S / (n : ℂ) with hudef
  have hconj : (starRingEnd ℂ) S * S = ((‖S‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have huS : u * S = (n : ℂ) := by
    rw [hudef, div_mul_eq_mul_div, hconj, h]
    push_cast
    field_simp
  have hnorm_u : ‖u‖ = 1 := by
    rw [hudef, norm_div, Complex.norm_conj, h, Complex.norm_natCast]
    field_simp
  have hsum : ∑ m ∈ range n, (u * e (f m)).re = (n : ℝ) := by
    have h1 : ∑ m ∈ range n, (u * e (f m)) = ((n : ℕ) : ℂ) := by
      rw [← Finset.mul_sum, ← hSdef, huS]
    have h2 : (∑ m ∈ range n, (u * e (f m))).re = (n : ℝ) := by rw [h1]; simp
    rw [← h2, Complex.re_sum]
  have hle : ∀ m ∈ range n, (u * e (f m)).re ≤ 1 := by
    intro m _
    calc (u * e (f m)).re ≤ ‖u * e (f m)‖ := Complex.re_le_norm _
      _ = 1 := by rw [norm_mul, hnorm_u, abs_e, one_mul]
  have hre : ∀ m ∈ range n, (u * e (f m)).re = 1 := by
    intro m hm
    by_contra hne
    have hlt : (u * e (f m)).re < 1 := lt_of_le_of_ne (hle m hm) hne
    have hstrict : ∑ j ∈ range n, (u * e (f j)).re < ∑ _j ∈ range n, (1 : ℝ) :=
      Finset.sum_lt_sum (fun i hi => hle i hi) ⟨m, hm, hlt⟩
    rw [hsum, Finset.sum_const, Finset.card_range] at hstrict
    simp at hstrict
  have hterm : ∀ m ∈ range n, u * e (f m) = 1 := by
    intro m hm
    have hn1 : ‖u * e (f m)‖ = 1 := by rw [norm_mul, hnorm_u, abs_e, one_mul]
    have hsq : (u * e (f m)).re ^ 2 + (u * e (f m)).im ^ 2 = 1 := by
      have hns := Complex.normSq_eq_norm_sq (u * e (f m))
      rw [hn1] at hns
      simpa [Complex.normSq_apply, sq] using hns
    rw [hre m hm] at hsq
    refine Complex.ext (by rw [hre m hm]; simp) ?_
    have him : (u * e (f m)).im = 0 := by nlinarith [sq_nonneg (u * e (f m)).im]
    rw [him]; simp
  intro m hm
  have hu1 : u = 1 := by
    have := hterm 0 (Finset.mem_range.2 hn)
    rwa [h0, mul_one] at this
  have := hterm m hm
  rwa [hu1, one_mul] at this

/-! ### Divisibility bookkeeping for the gcd of the digit set -/

/-- `IsIntMulZ θ m` says that `m θ` is an integer. -/
private def IsIntMulZ (θ : ℝ) (m : ℤ) : Prop := ∃ k : ℤ, (m : ℝ) * θ = (k : ℝ)

private theorem isIntMulZ_comb {θ : ℝ} {a b : ℤ} (ha : IsIntMulZ θ a) (hb : IsIntMulZ θ b)
    (x y : ℤ) : IsIntMulZ θ (x * a + y * b) := by
  obtain ⟨k₁, hk₁⟩ := ha
  obtain ⟨k₂, hk₂⟩ := hb
  refine ⟨x * k₁ + y * k₂, ?_⟩
  push_cast
  linear_combination (x : ℝ) * hk₁ + (y : ℝ) * hk₂

/-- If `g d · θ` is an integer for every `d` in a finite set `T`, then so is
`(gcd_{d ∈ T} g d) · θ`.  Bézout, by induction over `T`. -/
private theorem isIntMulZ_gcd (θ : ℝ) (g : ℕ → ℕ) (T : Finset ℕ)
    (h : ∀ d ∈ T, IsIntMulZ θ (g d)) : IsIntMulZ θ ((T.gcd g : ℕ) : ℤ) := by
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    have h1 : IsIntMulZ θ ((g a : ℕ) : ℤ) := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun d hd => h d (Finset.mem_insert_of_mem hd))
    rw [Finset.gcd_insert, gcd_eq_nat_gcd]
    have hbez : ((Nat.gcd (g a) (s.gcd g) : ℕ) : ℤ)
        = Nat.gcdA (g a) (s.gcd g) * ((g a : ℕ) : ℤ)
          + Nat.gcdB (g a) (s.gcd g) * ((s.gcd g : ℕ) : ℤ) := by
      rw [Nat.gcd_eq_gcd_ab]; ring
    rw [hbez]
    exact isIntMulZ_comb h1 h2 _ _

/-! ### The `n`-adic dichotomy -/

/-- **The dichotomy of the blueprint proof.**  If no `n^c θ` is an integer, then
`‖n^c θ‖ ≥ 1/(2n)` for infinitely many `c`: as long as the distance stays below `1/(2n)` it
is multiplied by `n` at each step, so it cannot stay there forever. -/
theorem exists_nrm_ge {n : ℕ} (hn : 2 ≤ n) {φ : ℝ} (hφ : ∀ c : ℕ, nrm ((n : ℝ) ^ c * φ) ≠ 0)
    (c₀ : ℕ) : ∃ c, c₀ ≤ c ∧ 1 / (2 * n) ≤ nrm ((n : ℝ) ^ c * φ) := by
  by_contra hcon
  push Not at hcon
  have hstep : ∀ j : ℕ,
      nrm ((n : ℝ) ^ (c₀ + j) * φ) = (n : ℝ) ^ j * nrm ((n : ℝ) ^ c₀ * φ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hrw : (n : ℝ) ^ (c₀ + (j + 1)) * φ = (n : ℝ) * ((n : ℝ) ^ (c₀ + j) * φ) := by
        ring
      rw [hrw, nrm_natCast_mul (by omega) (hcon (c₀ + j) (by omega)), ih, pow_succ]
      ring
  have hpos : 0 < nrm ((n : ℝ) ^ c₀ * φ) :=
    lt_of_le_of_ne (nrm_nonneg _) (Ne.symm (hφ c₀))
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  obtain ⟨j, hj⟩ :=
    pow_unbounded_of_one_lt (1 / (2 * (n : ℝ)) / nrm ((n : ℝ) ^ c₀ * φ)) hn1
  have hsmall := hcon (c₀ + j) (by omega)
  rw [hstep j] at hsmall
  rw [div_lt_iff₀ hpos] at hj
  linarith

namespace CantorData

variable (C : CantorData)

/-- The digit average `ρ θ = E_{d ∈ D} e (d θ)`, whose powers control the sums over blocks. -/
noncomputable def rho (θ : ℝ) : ℂ :=
  (C.delta : ℂ)⁻¹ * ∑ m ∈ range C.delta, e (C.digit m * θ)

/-- The normalized exponential sum over a full block of indices `[0, δ^ℓ)`. -/
noncomputable def blockAvg (β : ℝ) (ℓ : ℕ) : ℂ :=
  ((C.delta ^ ℓ : ℕ) : ℂ)⁻¹ * ∑ j ∈ range (C.delta ^ ℓ), e (β * C.enum j)

/-! ### The product formula over blocks -/

/-- Reindex a sum over `range (b * a)` by the base-`b` division `j = b * m + r`. -/
private theorem sum_range_mul_reindex {M : Type*} [AddCommMonoid M] (b a : ℕ) (f : ℕ → M) :
    ∑ j ∈ range (b * a), f j = ∑ m ∈ range a, ∑ r ∈ range b, f (b * m + r) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Peeling the top base-`δ` digit of the index: the sum of `e (β k_j)` over a block of length
`δ^(ℓ+1)` factors as a digit sum at scale `b^ℓ` times the sum over a block of length `δ^ℓ`.

This is `enum_block` (`lem:diff`(ii)) in the form the induction below needs. -/
theorem sum_block_succ (β : ℝ) (ℓ : ℕ) :
    ∑ j ∈ range (C.delta ^ (ℓ + 1)), e (β * C.enum j)
      = (∑ m ∈ range C.delta, e (β * (C.base ^ ℓ * C.digit m)))
        * ∑ r ∈ range (C.delta ^ ℓ), e (β * C.enum r) := by
  have hpow : C.delta ^ (ℓ + 1) = C.delta ^ ℓ * C.delta := by ring
  rw [hpow, sum_range_mul_reindex, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [C.enum_block ℓ m hr, C.enum_eq_digit hm]
  push_cast
  rw [← e_add]
  ring_nf

/-- **Equation `eq:Pell`.**  The average over a full block is a product of digit averages:
`P_ℓ β = ∏_{c < ℓ} ρ (b^c β)`. -/
theorem blockAvg_eq_prod (β : ℝ) (ℓ : ℕ) :
    C.blockAvg β ℓ = ∏ c ∈ range ℓ, C.rho (C.base ^ c * β) := by
  have hδ : (C.delta : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := C.two_le_delta; omega)
  induction ℓ with
  | zero => simp [blockAvg]
  | succ ℓ ih =>
    rw [Finset.prod_range_succ, ← ih, blockAvg, blockAvg, C.sum_block_succ, rho]
    have hcast : ((C.delta ^ (ℓ + 1) : ℕ) : ℂ) = (C.delta : ℂ) * ((C.delta ^ ℓ : ℕ) : ℂ) := by
      push_cast; ring
    rw [hcast, mul_inv]
    have hsum : ∑ m ∈ range C.delta, e (C.digit m * (C.base ^ ℓ * β))
        = ∑ m ∈ range C.delta, e (β * (C.base ^ ℓ * C.digit m)) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      congr 1
      ring
    rw [hsum]
    ring

/-- `‖ρ θ‖ ≤ 1`: an average of unit vectors. -/
theorem norm_rho_le_one (θ : ℝ) : ‖C.rho θ‖ ≤ 1 := by
  have hδ : 0 < C.delta := by have := C.two_le_delta; omega
  rw [rho, norm_mul, norm_inv]
  have h₁ : ‖∑ m ∈ range C.delta, e (C.digit m * θ)‖ ≤ C.delta := by
    calc ‖∑ m ∈ range C.delta, e (C.digit m * θ)‖
        ≤ ∑ m ∈ range C.delta, ‖e (C.digit m * θ)‖ := norm_sum_le _ _
      _ = C.delta := by simp
  have h₂ : ‖(C.delta : ℂ)‖ = (C.delta : ℝ) := by simp
  rw [h₂]
  rw [inv_mul_le_iff₀ (by exact_mod_cast hδ)]
  simpa using h₁

/-- `‖P_ℓ β‖ ≤ ∏_{c < ℓ} ‖ρ (b^c β)‖`; in particular the block averages are bounded by `1`. -/
theorem norm_blockAvg_le (β : ℝ) (ℓ : ℕ) :
    ‖C.blockAvg β ℓ‖ = ∏ c ∈ range ℓ, ‖C.rho (C.base ^ c * β)‖ := by
  rw [C.blockAvg_eq_prod, norm_prod]

theorem norm_blockAvg_le_one (β : ℝ) (ℓ : ℕ) : ‖C.blockAvg β ℓ‖ ≤ 1 := by
  rw [C.norm_blockAvg_le]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => C.norm_rho_le_one _)

/-! ### The window split

The estimate `eq:window-split` of the blueprint.  An arbitrary window of indices `[M, N)` is
cut into full blocks of length `δ^i`, on each of which the sum factors through `blockAvg`, plus
fewer than `2 δ^i` leftover indices at the two ends.  The resulting bound does not mention `M`:
this is where the uniformity of every average in this project comes from. -/

/-- Reindex a sum over `Ico (q * a) (q * b)` by `j = q * m + r`. -/
private theorem sum_Ico_mul_reindex {M : Type*} [AddCommMonoid M] (q : ℕ) {a b : ℕ}
    (hab : a ≤ b) (f : ℕ → M) :
    ∑ j ∈ Finset.Ico (q * a) (q * b), f j
      = ∑ m ∈ Finset.Ico a b, ∑ r ∈ range q, f (q * m + r) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hq : q * a ≤ q * b := Nat.mul_le_mul_left q hab
    rw [Nat.mul_succ, ← Finset.sum_Ico_consecutive f hq (by omega), ih,
      Finset.sum_Ico_succ_top hab]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    simp

/-- The sum over one full block, `enum_block` applied to every index of the block. -/
theorem sum_block_eq (β : ℝ) (i m : ℕ) :
    ∑ r ∈ range (C.delta ^ i), e (β * C.enum (C.delta ^ i * m + r))
      = e (β * (C.base ^ i * C.enum m)) * ((C.delta ^ i : ℕ) : ℂ) * C.blockAvg β i := by
  have hδ : 0 < C.delta := by have := C.two_le_delta; omega
  have hq : ((C.delta ^ i : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.pow_pos hδ).ne'
  rw [blockAvg]
  field_simp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [C.enum_block i m hr]
  push_cast
  rw [← e_add]
  ring_nf

/-- The trivial bound: a sum of `N - M` unit vectors. -/
theorem norm_sum_Ico_le_card (β : ℝ) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ico M N, e (β * C.enum n)‖ ≤ (N - M : ℕ) := by
  calc ‖∑ n ∈ Finset.Ico M N, e (β * C.enum n)‖
      ≤ ∑ n ∈ Finset.Ico M N, ‖e (β * C.enum n)‖ := norm_sum_le _ _
    _ = (N - M : ℕ) := by simp

/-- **The window split, `eq:window-split`.**  For every window of indices `[M, N)` and every
scale `i`,

  `‖∑_{M ≤ n < N} e (β k_n)‖ ≤ (N - M) * ‖P_i β‖ + 2 δ^i`.

The right-hand side does not depend on `M`.  That is the whole point: it is what makes the
averages of this project uniform in the starting index, and hence what turns positivity of an
average into a *syndetic* set of good indices. -/
theorem norm_sum_Ico_le (β : ℝ) (i M N : ℕ) :
    ‖∑ n ∈ Finset.Ico M N, e (β * C.enum n)‖
      ≤ (N - M : ℕ) * ‖C.blockAvg β i‖ + 2 * (C.delta ^ i : ℕ) := by
  have hδ : 0 < C.delta := by have := C.two_le_delta; omega
  set q := C.delta ^ i with hq_def
  have hq : 0 < q := Nat.pow_pos hδ
  set Mi := (M + q - 1) / q with hMi_def
  set Ni := N / q with hNi_def
  have hmod1 : q * Mi + (M + q - 1) % q = M + q - 1 := Nat.div_add_mod _ _
  have hmod1' : (M + q - 1) % q < q := Nat.mod_lt _ hq
  have hmod2 : q * Ni + N % q = N := Nat.div_add_mod _ _
  have hmod2' : N % q < q := Nat.mod_lt _ hq
  have hMlo : M ≤ q * Mi := by omega
  have hMhi : q * Mi ≤ M + q - 1 := by omega
  have hNlo : q * Ni ≤ N := by omega
  have hNhi : N < q * Ni + q := by omega
  have hnonneg : (0 : ℝ) ≤ ‖C.blockAvg β i‖ := norm_nonneg _
  rcases le_or_gt Mi Ni with hMN | hMN
  · -- The generic case: there is at least one full block.
    have h1 : M ≤ q * Mi := hMlo
    have h2 : q * Mi ≤ q * Ni := Nat.mul_le_mul_left q hMN
    have h3 : q * Ni ≤ N := hNlo
    have hsplit :
        ∑ n ∈ Finset.Ico M N, e (β * C.enum n)
          = (∑ n ∈ Finset.Ico M (q * Mi), e (β * C.enum n))
            + (∑ n ∈ Finset.Ico (q * Mi) (q * Ni), e (β * C.enum n))
            + ∑ n ∈ Finset.Ico (q * Ni) N, e (β * C.enum n) := by
      rw [← Finset.sum_Ico_consecutive _ h1 (h2.trans h3),
        ← Finset.sum_Ico_consecutive _ h2 h3, add_assoc]
    -- The middle part: full blocks, each contributing `q * blockAvg` up to a unit factor.
    have hmid : ‖∑ n ∈ Finset.Ico (q * Mi) (q * Ni), e (β * C.enum n)‖
        ≤ ((Ni - Mi : ℕ) : ℝ) * q * ‖C.blockAvg β i‖ := by
      rw [sum_Ico_mul_reindex q hMN]
      have hterm : ∀ m ∈ Finset.Ico Mi Ni,
          ∑ r ∈ range q, e (β * C.enum (q * m + r))
            = e (β * (C.base ^ i * C.enum m)) * ((q : ℕ) : ℂ) * C.blockAvg β i :=
        fun m _ => C.sum_block_eq β i m
      rw [Finset.sum_congr rfl hterm]
      calc ‖∑ m ∈ Finset.Ico Mi Ni,
              e (β * (C.base ^ i * C.enum m)) * ((q : ℕ) : ℂ) * C.blockAvg β i‖
          ≤ ∑ m ∈ Finset.Ico Mi Ni,
              ‖e (β * (C.base ^ i * C.enum m)) * ((q : ℕ) : ℂ) * C.blockAvg β i‖ :=
            norm_sum_le _ _
        _ = ∑ _m ∈ Finset.Ico Mi Ni, (q : ℝ) * ‖C.blockAvg β i‖ := by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [norm_mul, norm_mul, abs_e, one_mul]
            simp
        _ = ((Ni - Mi : ℕ) : ℝ) * q * ‖C.blockAvg β i‖ := by
            rw [Finset.sum_const, Nat.card_Ico]
            ring
    -- The two end pieces have fewer than `q` indices each.
    have hleft : ‖∑ n ∈ Finset.Ico M (q * Mi), e (β * C.enum n)‖ ≤ (q : ℝ) := by
      refine (C.norm_sum_Ico_le_card β _ _).trans ?_
      have : q * Mi - M ≤ q := by omega
      exact_mod_cast this
    have hright : ‖∑ n ∈ Finset.Ico (q * Ni) N, e (β * C.enum n)‖ ≤ (q : ℝ) := by
      refine (C.norm_sum_Ico_le_card β _ _).trans ?_
      have : N - q * Ni ≤ q := by omega
      exact_mod_cast this
    have hcount : ((Ni - Mi : ℕ) : ℝ) * q ≤ ((N - M : ℕ) : ℝ) := by
      have hnat : (Ni - Mi) * q ≤ N - M := by
        have h4 : (Ni - Mi) * q = Ni * q - Mi * q := Nat.sub_mul _ _ _
        have h5 : Ni * q = q * Ni := Nat.mul_comm _ _
        have h6 : Mi * q = q * Mi := Nat.mul_comm _ _
        omega
      exact_mod_cast hnat
    calc ‖∑ n ∈ Finset.Ico M N, e (β * C.enum n)‖
        ≤ ‖∑ n ∈ Finset.Ico M (q * Mi), e (β * C.enum n)‖
          + ‖∑ n ∈ Finset.Ico (q * Mi) (q * Ni), e (β * C.enum n)‖
          + ‖∑ n ∈ Finset.Ico (q * Ni) N, e (β * C.enum n)‖ := by
          rw [hsplit]
          exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ (q : ℝ) + ((Ni - Mi : ℕ) : ℝ) * q * ‖C.blockAvg β i‖ + (q : ℝ) := by
          gcongr
      _ ≤ (q : ℝ) + ((N - M : ℕ) : ℝ) * ‖C.blockAvg β i‖ + (q : ℝ) := by
          gcongr
      _ = ((N - M : ℕ) : ℝ) * ‖C.blockAvg β i‖ + 2 * q := by ring
  · -- Degenerate case: the window is too short to contain a full block, so `N - M < 2q`.
    have hstep : q * (Ni + 1) ≤ q * Mi := Nat.mul_le_mul_left q hMN
    have hstep' : q * (Ni + 1) = q * Ni + q := by ring
    have hshort : N - M ≤ 2 * q := by omega
    calc ‖∑ n ∈ Finset.Ico M N, e (β * C.enum n)‖
        ≤ ((N - M : ℕ) : ℝ) := C.norm_sum_Ico_le_card β M N
      _ ≤ 2 * (q : ℝ) := by exact_mod_cast hshort
      _ ≤ ((N - M : ℕ) : ℝ) * ‖C.blockAvg β i‖ + 2 * q := by
          have := mul_nonneg (Nat.cast_nonneg (α := ℝ) (N - M)) hnonneg
          linarith

/-! ### The uniform quantity `Φ` -/

/-- **Definition `def:Phi`.**  `Φ_L β = sup_{M ≥ 0} |E_{M ≤ n < M+L} e (β k_n)|`, the largest
size of an average of `e (β k_n)` over *any* window of `L` consecutive indices. -/
noncomputable def Phi (L : ℕ) (β : ℝ) : ℝ :=
  ⨆ M : ℕ, ‖(L : ℂ)⁻¹ * ∑ n ∈ Finset.Ico M (M + L), e (β * C.enum n)‖

theorem Phi_nonneg (L : ℕ) (β : ℝ) : 0 ≤ C.Phi L β := by
  refine Real.iSup_nonneg fun M => norm_nonneg _

/-- Each window average is bounded by `‖P_i β‖ + 2 δ^i / L`, uniformly in the window. -/
theorem norm_avg_le (β : ℝ) (i L M : ℕ) (hL : 0 < L) :
    ‖(L : ℂ)⁻¹ * ∑ n ∈ Finset.Ico M (M + L), e (β * C.enum n)‖
      ≤ ‖C.blockAvg β i‖ + 2 * (C.delta ^ i : ℕ) / L := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  rw [norm_mul, norm_inv]
  have hnorm : ‖(L : ℂ)‖ = (L : ℝ) := by simp
  rw [hnorm, inv_mul_le_iff₀ hL']
  have hsum := C.norm_sum_Ico_le β i M (M + L)
  have hcard : ((M + L - M : ℕ) : ℝ) = (L : ℝ) := by
    congr 1
    simp
  rw [hcard] at hsum
  calc ‖∑ n ∈ Finset.Ico M (M + L), e (β * C.enum n)‖
      ≤ (L : ℝ) * ‖C.blockAvg β i‖ + 2 * (C.delta ^ i : ℕ) := hsum
    _ = (L : ℝ) * (‖C.blockAvg β i‖ + 2 * (C.delta ^ i : ℕ) / L) := by
        field_simp

/-- **The uniform form of the window split.**  `Φ_L β ≤ ‖P_i β‖ + 2 δ^i / L` for every scale
`i`, with no dependence on the window. -/
theorem Phi_le (β : ℝ) (i L : ℕ) (hL : 0 < L) :
    C.Phi L β ≤ ‖C.blockAvg β i‖ + 2 * (C.delta ^ i : ℕ) / L := by
  refine Real.iSup_le (fun M => C.norm_avg_le β i L M hL) ?_
  have : (0 : ℝ) ≤ ‖C.blockAvg β i‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 2 * (C.delta ^ i : ℕ) / L := by positivity
  linarith

/-! ### The digit average is strictly smaller than one off the integers -/

/-- A general digit average `(1/δ) ∑_{m < δ} e (g m · θ)`.  The digit average `ρ` is the case
`g = digit`, and the reduced digit average `ρ'` the case `g = redDigit`. -/
noncomputable def avgE (g : ℕ → ℕ) (θ : ℝ) : ℂ :=
  (C.delta : ℂ)⁻¹ * ∑ m ∈ range C.delta, e (g m * θ)

theorem rho_eq_avgE (θ : ℝ) : C.rho θ = C.avgE C.digit θ := rfl

/-- Any digit average is an average of unit vectors, hence of modulus at most `1`. -/
theorem norm_avgE_le_one (g : ℕ → ℕ) (θ : ℝ) : ‖C.avgE g θ‖ ≤ 1 := by
  have hδ : 0 < C.delta := by have := C.two_le_delta; omega
  rw [avgE, norm_mul, norm_inv, Complex.norm_natCast]
  have h₁ : ‖∑ m ∈ range C.delta, e (g m * θ)‖ ≤ (C.delta : ℝ) := by
    calc ‖∑ m ∈ range C.delta, e (g m * θ)‖
        ≤ ∑ m ∈ range C.delta, ‖e (g m * θ)‖ := norm_sum_le _ _
      _ = (C.delta : ℝ) := by simp
  rw [inv_mul_le_iff₀ (by exact_mod_cast hδ)]
  simpa using h₁

/-- Each digit average is continuous. -/
theorem continuous_avgE (g : ℕ → ℕ) : Continuous (C.avgE g) := by
  unfold avgE
  exact continuous_const.mul
    (continuous_finsetSum _ fun m _ => continuous_e.comp (by fun_prop))

/-- Digit averages are `1`-periodic: shifting `θ` by an integer leaves them unchanged. -/
theorem avgE_sub_intCast (g : ℕ → ℕ) (θ : ℝ) (k : ℤ) :
    C.avgE g (θ - (k : ℝ)) = C.avgE g θ := by
  rw [avgE, avgE]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have hrw : (g m : ℝ) * (θ - (k : ℝ)) = (g m : ℝ) * θ + (((-(g m * k) : ℤ)) : ℝ) := by
    push_cast; ring
  rw [hrw, e_add, e_intCast, mul_one]

/-- **The equality case for the digit average.**  If `‖(1/δ) ∑ e (g m θ)‖ = 1` and `g 0 = 0`,
then every `g m · θ` is an integer: equality in the triangle inequality forces all the unit
vectors `e (g m θ)` to be equal, hence equal to `e 0 = 1`. -/
theorem isIntMul_of_norm_avgE_eq_one {g : ℕ → ℕ} (hg0 : g 0 = 0) {θ : ℝ}
    (h : ‖C.avgE g θ‖ = 1) : ∀ m ∈ range C.delta, ∃ k : ℤ, (g m : ℝ) * θ = (k : ℝ) := by
  have hδ : 0 < C.delta := by have := C.two_le_delta; omega
  have hδR : (0 : ℝ) < (C.delta : ℝ) := by exact_mod_cast hδ
  have hsum : ‖∑ m ∈ range C.delta, e ((g m : ℝ) * θ)‖ = (C.delta : ℝ) := by
    rw [avgE, norm_mul, norm_inv, Complex.norm_natCast] at h
    field_simp at h
    exact h
  have h0 : e ((g 0 : ℝ) * θ) = 1 := by rw [hg0]; simp
  intro m hm
  exact e_eq_one_iff.1 (e_eq_one_of_norm_sum hδ (fun m => (g m : ℝ) * θ) h0 hsum m hm)

/-! ### Reducing the digit set by its gcd -/

/-- `s = gcd D`, the greatest common divisor of the digit set. -/
noncomputable def gcdDigits : ℕ := (range C.delta).gcd C.digit

theorem gcdDigits_dvd {m : ℕ} (hm : m < C.delta) : C.gcdDigits ∣ C.digit m :=
  Finset.gcd_dvd (Finset.mem_range.2 hm)

theorem gcdDigits_pos : 0 < C.gcdDigits := by
  rcases Nat.eq_zero_or_pos C.gcdDigits with h | h
  · exfalso
    have h1 : C.digit 1 = 0 := by
      have hdvd := C.gcdDigits_dvd (show 1 < C.delta from C.two_le_delta)
      rw [h] at hdvd
      exact Nat.eq_zero_of_zero_dvd hdvd
    have h2 := C.one_le_digit (by norm_num) C.two_le_delta
    omega
  · exact h

/-- The reduced digits `d_m / s`. -/
noncomputable def redDigit (m : ℕ) : ℕ := C.digit m / C.gcdDigits

@[simp] theorem redDigit_zero : C.redDigit 0 = 0 := by simp [redDigit]

theorem gcdDigits_mul_redDigit {m : ℕ} (hm : m < C.delta) :
    C.gcdDigits * C.redDigit m = C.digit m :=
  Nat.mul_div_cancel' (C.gcdDigits_dvd hm)

/-- The reduced digit set has gcd `1`.  This is what replaces the blueprint's passage to the
auxiliary Cantor set `C_{b,D'}`: only the digit averages are reduced, not the Cantor set. -/
theorem gcd_redDigit : (range C.delta).gcd C.redDigit = 1 := by
  set g := (range C.delta).gcd C.redDigit with hg
  have key : g * C.gcdDigits ∣ C.gcdDigits := by
    rw [gcdDigits]
    refine Finset.dvd_gcd ?_
    intro m hm
    rw [Finset.mem_range] at hm
    rw [← C.gcdDigits_mul_redDigit hm, mul_comm C.gcdDigits]
    exact mul_dvd_mul (Finset.gcd_dvd (Finset.mem_range.2 hm)) dvd_rfl
  have hs := C.gcdDigits_pos
  have h1 : g * C.gcdDigits ∣ 1 * C.gcdDigits := by rwa [one_mul]
  exact Nat.dvd_one.1 ((Nat.mul_dvd_mul_iff_right hs).1 h1)

/-- The reduced digit average `ρ'`, so that `ρ θ = ρ' (s θ)`. -/
noncomputable def rhoRed (θ : ℝ) : ℂ := C.avgE C.redDigit θ

theorem continuous_rhoRed : Continuous C.rhoRed := C.continuous_avgE _

theorem rhoRed_fract (θ : ℝ) : C.rhoRed (Int.fract θ) = C.rhoRed θ := by
  rw [rhoRed, rhoRed, show Int.fract θ = θ - ((⌊θ⌋ : ℤ) : ℝ) from rfl,
    C.avgE_sub_intCast]

/-- The digit average factors through the reduced one: `ρ θ = ρ' (s θ)`. -/
theorem rho_eq_rhoRed (θ : ℝ) : C.rho θ = C.rhoRed ((C.gcdDigits : ℝ) * θ) := by
  rw [rho_eq_avgE, rhoRed, avgE, avgE]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  congr 1
  have hd : (C.digit m : ℝ) = (C.gcdDigits : ℝ) * (C.redDigit m : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (C.gcdDigits_mul_redDigit hm).symm
  rw [hd]; ring

/-- **The digit average is strictly smaller than `1` off the integers.** -/
theorem norm_rhoRed_lt_one {θ : ℝ} (hθ : ∀ k : ℤ, θ ≠ (k : ℝ)) : ‖C.rhoRed θ‖ < 1 := by
  rcases lt_or_eq_of_le (C.norm_avgE_le_one C.redDigit θ) with h | h
  · exact h
  · exfalso
    have hall := C.isIntMul_of_norm_avgE_eq_one (g := C.redDigit) (by simp) h
    have hgcd := isIntMulZ_gcd θ C.redDigit (range C.delta) (fun d hd => by
      obtain ⟨k, hk⟩ := hall d hd
      exact ⟨k, by push_cast; linarith⟩)
    rw [gcd_redDigit] at hgcd
    obtain ⟨k, hk⟩ := hgcd
    exact hθ k (by simpa using hk)

/-- **The uniform gap.**  For every `η > 0` there is `κ > 0` with `‖ρ' θ‖ ≤ 1 - κ` whenever
`θ` is at distance at least `η` from the integers: continuity of `ρ'` plus compactness of
`[η, 1 - η]`. -/
theorem exists_kappa {η : ℝ} (hη : 0 < η) :
    ∃ κ > 0, ∀ θ : ℝ, η ≤ nrm θ → ‖C.rhoRed θ‖ ≤ 1 - κ := by
  set η₀ : ℝ := min η (1 / 2) with hη₀def
  have hη₀ : 0 < η₀ := lt_min hη (by norm_num)
  have hη₀half : η₀ ≤ 1 / 2 := min_le_right _ _
  have hne : (Set.Icc η₀ (1 - η₀)).Nonempty := ⟨η₀, by constructor <;> linarith⟩
  obtain ⟨θ₀, hθ₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn hne (C.continuous_rhoRed.norm.continuousOn)
  have h0 : (0 : ℝ) < θ₀ := lt_of_lt_of_le hη₀ hθ₀.1
  have h1 : θ₀ < 1 := lt_of_le_of_lt hθ₀.2 (by linarith)
  have hlt : ‖C.rhoRed θ₀‖ < 1 := by
    refine C.norm_rhoRed_lt_one fun k hk => ?_
    rw [hk] at h0 h1
    have hk0 : (0 : ℤ) < k := by exact_mod_cast h0
    have hk1 : k < 1 := by exact_mod_cast h1
    omega
  refine ⟨1 - ‖C.rhoRed θ₀‖, by linarith, fun θ hθ => ?_⟩
  have hθ' : η₀ ≤ nrm θ := le_trans (min_le_left _ _) hθ
  have hfr : Int.fract θ ∈ Set.Icc η₀ (1 - η₀) := fract_mem_Icc hθ'
  have hbound : ‖C.rhoRed (Int.fract θ)‖ ≤ ‖C.rhoRed θ₀‖ := hmax hfr
  rw [C.rhoRed_fract] at hbound
  linarith

/-! ### The limit of the block averages, and of `Φ` -/

/-- **The exceptional set `E₀`.**  Those `β` for which `gcd(D) · β` is a `b`-adic rational
modulo `1`. -/
def excSet : Set ℝ :=
  {β : ℝ | ∃ c : ℕ, ∃ k : ℤ, (C.base : ℝ) ^ c * ((C.gcdDigits : ℝ) * β) = (k : ℝ)}

/-- For `β ∉ E₀` the block averages `P_ℓ β` are eventually as small as we please. -/
theorem exists_norm_blockAvg_lt {β : ℝ} (hβ : β ∉ C.excSet) {ε : ℝ} (hε : 0 < ε) :
    ∃ i, ‖C.blockAvg β i‖ < ε := by
  set φ : ℝ := (C.gcdDigits : ℝ) * β with hφ
  have hb2 : 2 ≤ C.base := by have := C.three_le_base; omega
  have hbR : (0 : ℝ) < (C.base : ℝ) := by
    have : 0 < C.base := by omega
    exact_mod_cast this
  have hne : ∀ c : ℕ, nrm ((C.base : ℝ) ^ c * φ) ≠ 0 := by
    intro c hc
    obtain ⟨k, hk⟩ := nrm_eq_zero_iff.1 hc
    exact hβ ⟨c, k, hk⟩
  have hη : (0 : ℝ) < 1 / (2 * (C.base : ℝ)) := by positivity
  obtain ⟨κ, hκ, hκle⟩ := C.exists_kappa hη
  set S : Set ℕ := {c : ℕ | 1 / (2 * (C.base : ℝ)) ≤ nrm ((C.base : ℝ) ^ c * φ)} with hS
  have hSinf : S.Infinite := by
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨M, hM⟩
    obtain ⟨c, hc, hcge⟩ := exists_nrm_ge hb2 hne (M + 1)
    have : c ≤ M := hM (show c ∈ S from hcge)
    omega
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (show 1 - κ < 1 by linarith)
  obtain ⟨t, htS, htcard⟩ := hSinf.exists_subset_card_eq N
  obtain ⟨ℓ, htℓ⟩ := t.exists_nat_subset_range
  refine ⟨ℓ, ?_⟩
  have hfac : ∀ c : ℕ,
      ‖C.rho ((C.base : ℝ) ^ c * β)‖ = ‖C.rhoRed ((C.base : ℝ) ^ c * φ)‖ := by
    intro c
    rw [C.rho_eq_rhoRed]
    congr 2
    rw [hφ]; ring
  rw [C.norm_blockAvg_le]
  have hsub : ∏ c ∈ range ℓ, ‖C.rho ((C.base : ℝ) ^ c * β)‖
      ≤ ∏ c ∈ t, ‖C.rho ((C.base : ℝ) ^ c * β)‖ := by
    rw [← Finset.prod_sdiff htℓ]
    have h1 : ∏ c ∈ range ℓ \ t, ‖C.rho ((C.base : ℝ) ^ c * β)‖ ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => C.norm_rho_le_one _)
    have h2 : 0 ≤ ∏ c ∈ t, ‖C.rho ((C.base : ℝ) ^ c * β)‖ :=
      Finset.prod_nonneg fun i _ => norm_nonneg _
    nlinarith
  have hprod : ∏ c ∈ t, ‖C.rho ((C.base : ℝ) ^ c * β)‖ ≤ (1 - κ) ^ N := by
    calc ∏ c ∈ t, ‖C.rho ((C.base : ℝ) ^ c * β)‖
        ≤ ∏ _c ∈ t, (1 - κ) := by
          refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi => ?_)
          rw [hfac]
          exact hκle _ (htS (Finset.mem_coe.2 hi))
      _ = (1 - κ) ^ N := by rw [Finset.prod_const, htcard]
  linarith [hsub, hprod, hN]

/-- **Lemma `lem:irrational`.**  For `β` outside the countable exceptional set `E₀`, the
uniform averages `Φ_L β` tend to `0`. -/
theorem tendsto_Phi_zero {β : ℝ} (hβ : β ∉ C.excSet) :
    Filter.Tendsto (fun L => C.Phi L β) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨i, hi⟩ := C.exists_norm_blockAvg_lt hβ (half_pos hε)
  set X : ℝ := ((C.delta ^ i : ℕ) : ℝ) with hX
  refine ⟨⌈4 * X / ε⌉₊ + 1, fun L hL => ?_⟩
  have hLpos : 0 < L := by omega
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hceil : 4 * X / ε ≤ (L : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    have : (⌈4 * X / ε⌉₊ : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : ⌈4 * X / ε⌉₊ ≤ L)
    exact this
  have h2 : 2 * X / (L : ℝ) ≤ ε / 2 := by
    rw [div_le_iff₀ hLR]
    rw [div_le_iff₀ hε] at hceil
    linarith
  have hbound := C.Phi_le β i L hLpos
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (C.Phi_nonneg L β)]
  linarith

end CantorData

end CantorSzemeredi

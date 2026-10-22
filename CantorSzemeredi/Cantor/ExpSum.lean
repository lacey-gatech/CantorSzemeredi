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

end CantorData

end CantorSzemeredi

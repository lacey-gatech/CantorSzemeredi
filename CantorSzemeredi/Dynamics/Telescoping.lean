/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import Mathlib

/-!
# Telescoping for products

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:telescoping`.

The telescoping identity for a difference of products, and its consequence for products of
values in `[-1, 1]`.
-/

namespace CantorSzemeredi

open Finset

/-- **Lemma `lem:telescoping`, the identity.**
`∏ a - ∏ b = ∑_j (∏_{i<j} b_i) (a_j - b_j) (∏_{j<i<t} a_i)`. -/
theorem prod_sub_prod_telescope {R : Type*} [CommRing R] (t : ℕ) (a b : ℕ → R) :
    ∏ j ∈ range t, a j - ∏ j ∈ range t, b j
      = ∑ j ∈ range t, (∏ i ∈ range j, b i) * (a j - b j) * ∏ i ∈ Ico (j + 1) t, a i := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, prod_range_succ, prod_range_succ]
    have hsum : ∑ j ∈ range t, (∏ i ∈ range j, b i) * (a j - b j) * ∏ i ∈ Ico (j + 1) (t + 1), a i
        = (∑ j ∈ range t, (∏ i ∈ range j, b i) * (a j - b j) * ∏ i ∈ Ico (j + 1) t, a i) * a t := by
      rw [sum_mul]
      refine sum_congr rfl fun j hj => ?_
      have hjt : j + 1 ≤ t := Nat.succ_le_of_lt (mem_range.1 hj)
      rw [prod_Ico_succ_top hjt]
      ring
    have hlast : ∏ i ∈ Ico (t + 1) (t + 1), a i = 1 := by simp
    rw [hsum, hlast, ← ih]
    ring

/-- The product of values in `[-1,1]` lies in `[-1,1]`. -/
theorem abs_prod_le_one {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, |f i| ≤ 1) :
    |∏ i ∈ s, f i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ => hf i

/-- **Lemma `lem:telescoping`, the bound.**  For values in `[-1,1]`,
`|∏ a - ∏ b| ≤ ∑ |a_j - b_j|`. -/
theorem abs_prod_sub_prod_le_sum' (t : ℕ) (a b : ℕ → ℝ) (ha : ∀ j, |a j| ≤ 1)
    (hb : ∀ j, |b j| ≤ 1) :
    |∏ j ∈ range t, a j - ∏ j ∈ range t, b j| ≤ ∑ j ∈ range t, |a j - b j| := by
  rw [prod_sub_prod_telescope t a b]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul]
  have h1 : |∏ i ∈ range j, b i| ≤ 1 := abs_prod_le_one _ _ hb
  have h2 : |∏ i ∈ Ico (j + 1) t, a i| ≤ 1 := abs_prod_le_one _ _ ha
  have h3 : |∏ i ∈ range j, b i| * |a j - b j| ≤ |a j - b j| :=
    mul_le_of_le_one_left (abs_nonneg _) h1
  have h4 : |∏ i ∈ range j, b i| * |a j - b j| * |∏ i ∈ Ico (j + 1) t, a i|
      ≤ |∏ i ∈ range j, b i| * |a j - b j| :=
    mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) h2
  linarith

end CantorSzemeredi

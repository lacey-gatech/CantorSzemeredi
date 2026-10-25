/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMInduction

/-!
# The correlation on one class of indices

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`, Step 1 ("the correlation on one
class").  For a fixed shift `h` and a fixed class of indices, the correlation
`⟨u_{n+h}, u_n⟩` of the products `u_n = ∏ T^{s_j k_n} f_j` is an integral of a product of
the functions `F_j = f_j · T^{s_j D} f_j`, with the shift `T^{(s_j - s_1) k_n}` on the `j`-th
factor.
-/

namespace CantorSzemeredi

open MeasureTheory Finset

namespace MPS

/-- Undoing `T^r` by `T^{-r}` leaves `T^{a - r}`, when `r ≤ a`. -/
theorem T_iterate_Tinv_iterate (S : MPS) (r a : ℕ) (x : S.X) (h : r ≤ a) :
    S.T^[a] (S.Tinv^[r] x) = S.T^[a - r] x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hR : ∀ (n : ℕ) (y : S.X), S.T^[n] (S.Tinv^[n] y) = y :=
    fun n => Function.LeftInverse.iterate S.T_Tinv n
  rw [Nat.add_sub_cancel_left, add_comm r d, Function.iterate_add_apply, hR]

/-- Invariance of the integral of a product of shifted factors under the common shift
`T^{-r}`, where `r` is at most every exponent. -/
theorem integral_prod_shift (S : MPS) (G : ℕ → S.X → ℝ) (t r : ℕ) (a : ℕ → ℕ)
    (ha : ∀ j < t, r ≤ a j) :
    ∫ x, ∏ j ∈ range t, G j (S.T^[a j] x) ∂S.m
      = ∫ x, ∏ j ∈ range t, G j (S.T^[a j - r] x) ∂S.m := by
  have hmp : MeasurePreserving (S.pow r).measurableEquiv.symm S.m S.m :=
    (S.pow r).measurePreserving_Tinv
  have hcoe : ⇑(S.pow r).measurableEquiv.symm = S.Tinv^[r] := S.pow_Tinv r
  have key : ∀ g : S.X → ℝ, ∫ x, g (S.Tinv^[r] x) ∂S.m = ∫ x, g x ∂S.m := fun g => by
    rw [← hcoe]
    exact hmp.integral_comp' g
  calc ∫ x, ∏ j ∈ range t, G j (S.T^[a j] x) ∂S.m
      = ∫ x, (fun y => ∏ j ∈ range t, G j (S.T^[a j] y)) (S.Tinv^[r] x) ∂S.m :=
        (key (fun y => ∏ j ∈ range t, G j (S.T^[a j] y))).symm
    _ = ∫ x, ∏ j ∈ range t, G j (S.T^[a j - r] x) ∂S.m := by
        congr 1
        funext x
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [T_iterate_Tinv_iterate S r (a j) x (ha j (mem_range.1 hj))]

/-- **Step 1, the correlation on one class.**  If `k' = k + D`, the correlation of the products
`∏_j T^{s_j k'} f_j` and `∏_j T^{s_j k} f_j` equals the integral of the product over `j` of
`f_j · (T^{s_j D} f_j)`, each factor shifted by `T^{(s_j - s_0) k}`. -/
theorem integral_corr_eq_shifted (S : MPS) (s : ℕ → ℕ) (t : ℕ) (hs : GoodExp s t) (f : ℕ → S.X → ℝ)
    (k D : ℕ) :
    ∫ x, (∏ j ∈ range t, f j (S.T^[s j * (k + D)] x))
        * (∏ j ∈ range t, f j (S.T^[s j * k] x)) ∂S.m
      = ∫ x, ∏ j ∈ range t,
          (f j (S.T^[s j * k - s 0 * k] x)
            * f j (S.T^[s j * D] (S.T^[s j * k - s 0 * k] x))) ∂S.m := by
  have hpt : ∀ x, (∏ j ∈ range t, f j (S.T^[s j * (k + D)] x))
      * (∏ j ∈ range t, f j (S.T^[s j * k] x))
      = ∏ j ∈ range t, (fun y => f j y * f j (S.T^[s j * D] y)) (S.T^[s j * k] x) := by
    intro x
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hit : S.T^[s j * (k + D)] x = S.T^[s j * D] (S.T^[s j * k] x) := by
      rw [mul_add, add_comm, Function.iterate_add_apply]
    simp only [hit]
    ring
  have ha : ∀ j < t, s 0 * k ≤ s j * k := fun j hj => Nat.mul_le_mul_right k (by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact le_rfl
    · exact (hs.2 0 j hpos hj).le)
  calc ∫ x, (∏ j ∈ range t, f j (S.T^[s j * (k + D)] x))
        * (∏ j ∈ range t, f j (S.T^[s j * k] x)) ∂S.m
      = ∫ x, ∏ j ∈ range t, (fun y => f j y * f j (S.T^[s j * D] y)) (S.T^[s j * k] x) ∂S.m := by
        congr 1
        funext x
        exact hpt x
    _ = _ := integral_prod_shift S (fun j y => f j y * f j (S.T^[s j * D] y)) t (s 0 * k)
        (fun j => s j * k) ha

end MPS

end CantorSzemeredi

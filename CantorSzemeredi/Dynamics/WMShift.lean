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

open MeasureTheory Finset Filter Topology

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

/-- Splitting a shift along a block: `T^{e(BA + C)} x = T^{eC} (T^{B(eA)} x)`, where
`T^{B·p}` is the `p`-th power of the system `S.pow B`. -/
theorem iterate_block_comm (S : MPS) (e B A C : ℕ) (x : S.X) :
    S.T^[e * (B * A + C)] x = S.T^[e * C] ((S.pow B).T^[e * A] x) := by
  have h : e * (B * A + C) = e * C + B * (e * A) := by ring
  rw [h, Function.iterate_add_apply, Function.iterate_mul S.T B (e * A)]
  rfl

/-- **Step 1, re-indexing along a class.**  For `n = δ^ℓ a + c` with `c < δ^ℓ`, the shifted
product at `k_n` equals the product of the functions `F_j ∘ T^{(s_j - s_0) k_c}` evaluated at
the shifts by `T^{b^ℓ}` (the system `S.pow (b^ℓ)`) with exponents `(s_j - s_0) k_a`. -/
theorem prod_reindex (C : CantorData) (S : MPS) (s : ℕ → ℕ) (t ℓ c a : ℕ)
    (hc : c < C.delta ^ ℓ) (F : ℕ → S.X → ℝ) (x : S.X) :
    ∏ j ∈ range t, F j (S.T^[(s j - s 0) * C.enum (C.delta ^ ℓ * a + c)] x)
      = ∏ j ∈ range t,
          (fun y => F j (S.T^[(s j - s 0) * C.enum c] y))
            ((S.pow (C.base ^ ℓ)).T^[(s j - s 0) * C.enum a] x) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [C.enum_block ℓ a hc, iterate_block_comm]

/-- The weak-mixing hypothesis passes to the power system `S.pow k` with the factors `D.toPow k`,
`E.toPow k` (blueprint `lem:powers`(2), via `CondWeaklyMixing.pow`). -/
theorem wmHyp_pow {S : MPS.{0}} {D E : Factor S} (hWM : S.WMHyp D E) {k : ℕ} (hk : 1 ≤ k) :
    (S.pow k).WMHyp (D.toPow k) (E.toPow k) := by
  intro g hg hK hmean
  exact CondWeaklyMixing.pow (hWM g hg hK hmean) hk

/-- `T` is measurable for the sub-σ-algebra `E.σ`, by invariance of the factor. -/
theorem measurable_T_factor {S : MPS.{0}} (E : Factor S) : Measurable[E.σ, E.σ] S.T :=
  fun s hs => (E.invariant s).2 hs

/-- Composition with an iterate preserves `E`-measurability. -/
theorem measurable_comp_iter {S : MPS.{0}} (E : Factor S) {f : S.X → ℝ}
    (hf : Measurable[E.σ] f) (n : ℕ) : Measurable[E.σ] (f ∘ S.T^[n]) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [Function.iterate_succ, ← Function.comp_assoc]
    exact ih.comp (measurable_T_factor E)

/-- Clipping to `[-K, K]` keeps a bound by `K ≥ 0`. -/
theorem abs_clip_le {K : ℝ} (hK0 : 0 ≤ K) (y : ℝ) : |max (-K) (min K y)| ≤ K :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Clipping does not change a function that is a.e. bounded by `K`. -/
theorem clip_ae_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : ℝ} {u : α → ℝ}
    (h : ∀ᵐ x ∂μ, |u x| ≤ K) :
    (fun x => max (-K) (min K (u x))) =ᵐ[μ] u := by
  filter_upwards [h] with x hx
  rw [min_eq_right (abs_le.1 hx).2, max_eq_right (abs_le.1 hx).1]

/-- **Step 1, the induction hypothesis on the re-indexed tuple.**  The tuple `i ↦ F_{i+1} ∘
T^{(s_{i+1} - s_0) k_c}` on the system `S.pow (b^ℓ)` with exponents `s_{i+1} - s_0` satisfies
the difference form at `t`, against its clipped conditional expectations.  This is the
hypothesis `(IH-a)` of `lem:wm-main`, obtained from `DiffForm C t` (the induction hypothesis
`P(t)` for the power system). -/
theorem reindexed_diff (C : CantorData) (t : ℕ) (hIH : DiffForm C t) (S : MPS.{0})
    (s : ℕ → ℕ) (hs : GoodExp s (t + 1)) (D E : Factor S) (hDE : D.σ ≤ E.σ)
    (hWM : S.WMHyp D E) (m : ℕ) (hm : 1 ≤ m) (c : ℕ) (F : ℕ → S.X → ℝ) (K : ℝ) (hK0 : 0 ≤ K)
    (hFm : ∀ j, j < t + 1 → Measurable[E.σ] (F j))
    (hFb : ∀ j, j < t + 1 → ∀ x, |F j x| ≤ K) :
    Tendsto (fun p : ℕ × ℕ => eLpNorm
        (avgProd (S := S.pow m) C (fun i => s (i + 1) - s 0) t
            (fun i x => F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum c] x)) p
          - avgProd (S := S.pow m) C (fun i => s (i + 1) - s 0) t
            (fun i x => max (-K) (min K (S.m[fun y => F (i + 1) (S.T^[(s (i + 1) - s 0)
              * C.enum c] y) | D.σ] x))) p) 2 S.m)
      uniformFilter (𝓝 0) := by
  have hs' : GoodExp (fun i => s (i + 1) - s 0) t := by
    refine ⟨fun i hi => ?_, fun i j hij hj => ?_⟩
    · have := hs.2 0 (i + 1) (by omega) (by omega)
      show 1 ≤ s (i + 1) - s 0
      omega
    · have h1 := hs.2 0 (i + 1) (by omega) (by omega)
      have h2 := hs.2 (i + 1) (j + 1) (by omega) (by omega)
      show s (i + 1) - s 0 < s (j + 1) - s 0
      omega
  have hH : ∀ i, i < t → Measurable[E.σ] (fun x => F (i + 1) (S.T^[(s (i + 1) - s 0)
      * C.enum c] x)) := fun i hi => measurable_comp_iter E (hFm (i + 1) (by omega)) _
  have hHb : ∀ i, i < t → ∀ x, |F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum c] x)| ≤ K :=
    fun i hi x => hFb (i + 1) (by omega) _
  have hint : ∀ i, i < t → Integrable (fun x => F (i + 1) (S.T^[(s (i + 1) - s 0)
      * C.enum c] x)) S.m := fun i hi =>
    integrable_of_bdd_const ((hH i hi).mono E.le le_rfl) (fun x => hHb i hi x)
  have hmemL : ∀ i, i < t → MemLp (fun x => F (i + 1) (S.T^[(s (i + 1) - s 0)
      * C.enum c] x)) 2 S.m := fun i hi =>
    MemLp.of_bound ((hH i hi).mono E.le le_rfl).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hHb i hi x)
  have hcond : ∀ i, i < t → ∀ᵐ x ∂S.m,
      |S.m[fun y => F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum c] y) | D.σ] x| ≤ K :=
    fun i hi => (condExp_facts D (hint i hi) (hHb i hi) (hmemL i hi) 0).1
  have hgm : ∀ i, i < t → Measurable[D.σ] (fun x => max (-K) (min K
      (S.m[fun y => F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum c] y) | D.σ] x))) :=
    fun i _ => Measurable.max measurable_const
      (Measurable.min measurable_const stronglyMeasurable_condExp.measurable)
  have hEg : ∀ i, i < t → S.m[fun y => F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum c] y) | D.σ]
      =ᵐ[S.m] fun x => max (-K) (min K
        (S.m[fun y => F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum c] y) | D.σ] x)) :=
    fun i hi => (clip_ae_eq (hcond i hi)).symm
  have hB : ∃ B : ℝ, ∀ i, i < t → ∀ x, |F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum c] x)| ≤ B
      ∧ |max (-K) (min K (S.m[fun y => F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum c] y)
          | D.σ] x))| ≤ B :=
    ⟨K, fun i hi x => ⟨hHb i hi x, abs_clip_le hK0 _⟩⟩
  exact hIH (S.pow m) (D.toPow m) (E.toPow m) hDE (wmHyp_pow hWM hm) (fun i => s (i + 1) - s 0)
    hs' (fun i x => F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum c] x))
    (fun i x => max (-K) (min K (S.m[fun y => F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum c] y)
      | D.σ] x)))
    (fun i hi => hH i hi) (fun i hi => hgm i hi) hB hEg

end MPS

end CantorSzemeredi

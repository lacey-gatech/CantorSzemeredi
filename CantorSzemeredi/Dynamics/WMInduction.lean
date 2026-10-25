/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMMain
import CantorSzemeredi.Dynamics.Telescoping

/-!
# The induction for the main weak-mixing estimate

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`.

The statement is proved by induction on the number of factors.  This file contains the
reduction from the star form (one factor of conditional expectation zero) to the difference form
(telescoping), which the induction hypothesis is applied in.
-/

namespace CantorSzemeredi

open Finset MeasureTheory Filter Topology

/-- Splitting the product of a modified tuple at the index `j₀`: the factors before `j₀` are
`b`, the factor at `j₀` is `a - b`, and the factors after are `a`. -/
theorem prod_range_modified (t j₀ : ℕ) (hj : j₀ < t) (a b : ℕ → ℝ) :
    ∏ j ∈ range t, (if j = j₀ then a j - b j else if j < j₀ then b j else a j)
      = (∏ j ∈ range j₀, b j) * (a j₀ - b j₀) * ∏ j ∈ Ico (j₀ + 1) t, a j := by
  rw [← prod_range_mul_prod_Ico _ (Nat.succ_le_of_lt hj)]
  have h1 : ∏ j ∈ range j₀, (if j = j₀ then a j - b j else if j < j₀ then b j else a j)
      = ∏ j ∈ range j₀, b j := by
    refine prod_congr rfl fun j hj' => ?_
    have hlt : j < j₀ := mem_range.1 hj'
    rw [if_neg (Nat.ne_of_lt hlt), if_pos hlt]
  have h2 : ∏ j ∈ Ico (j₀ + 1) t, (if j = j₀ then a j - b j else if j < j₀ then b j else a j)
      = ∏ j ∈ Ico (j₀ + 1) t, a j := by
    refine prod_congr rfl fun j hj' => ?_
    have hgt : j₀ < j := by
      have := (mem_Ico.1 hj').1
      omega
    rw [if_neg (Nat.ne_of_gt hgt), if_neg (not_lt.2 hgt.le)]
  have h3 : (if j₀ = j₀ then a j₀ - b j₀ else if j₀ < j₀ then b j₀ else a j₀) = a j₀ - b j₀ := by
    rw [if_pos rfl]
  rw [prod_range_succ, h1, h2, h3]

namespace MPS

variable {S : MPS}

/-- The average over the window `[M, N)` of the product `∏_{j < t} φ_j(T^{s_j k_n} x)`, where
`k_n` is the enumeration of the Cantor set. -/
noncomputable def avgProd (C : CantorData) (s : ℕ → ℕ) (t : ℕ) (φ : ℕ → S.X → ℝ)
    (p : ℕ × ℕ) : S.X → ℝ :=
  fun x => ((p.2 - p.1 : ℕ) : ℝ)⁻¹ *
    ∑ n ∈ Finset.Ico p.1 p.2, ∏ j ∈ Finset.range t, φ j (S.T^[s j * C.enum n] x)

/-- The tuple obtained from `f` by replacing the factor at `j₀` by `f - g` and the factors before
`j₀` by `g`. -/
def tupleAt (t j₀ : ℕ) (f g : ℕ → S.X → ℝ) : ℕ → S.X → ℝ :=
  fun j x => if j = j₀ then f j x - g j x else if j < j₀ then g j x else f j x

/-- Pointwise telescoping along a sequence of points. -/
theorem prod_telescope_points (t : ℕ) (f g : ℕ → S.X → ℝ) (y : ℕ → S.X) :
    ∏ j ∈ Finset.range t, f j (y j) - ∏ j ∈ Finset.range t, g j (y j)
      = ∑ j₀ ∈ Finset.range t, ∏ j ∈ Finset.range t, tupleAt t j₀ f g j (y j) := by
  rw [prod_sub_prod_telescope t (fun j => f j (y j)) (fun j => g j (y j))]
  refine Finset.sum_congr rfl fun j₀ hj₀ => ?_
  have hj : j₀ < t := Finset.mem_range.1 hj₀
  have := prod_range_modified t j₀ hj (fun j => f j (y j)) (fun j => g j (y j))
  simp only [tupleAt]
  rw [this]

/-- The average of a difference of products is the sum of the averages of the modified tuples. -/
theorem avgProd_sub_eq_sum (C : CantorData) (s : ℕ → ℕ) (t : ℕ) (f g : ℕ → S.X → ℝ)
    (p : ℕ × ℕ) :
    avgProd C s t f p - avgProd C s t g p
      = ∑ j₀ ∈ Finset.range t, avgProd C s t (tupleAt t j₀ f g) p := by
  funext x
  simp only [avgProd, Pi.sub_apply, Finset.sum_apply]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hpt : ∀ n, ∏ j ∈ Finset.range t, f j (S.T^[s j * C.enum n] x)
        - ∏ j ∈ Finset.range t, g j (S.T^[s j * C.enum n] x)
      = ∑ j₀ ∈ Finset.range t, ∏ j ∈ Finset.range t, tupleAt t j₀ f g j
          (S.T^[s j * C.enum n] x) := fun n =>
    prod_telescope_points t f g (fun j => S.T^[s j * C.enum n] x)
  simp only [hpt]
  rw [Finset.sum_comm, Finset.mul_sum]

end MPS

namespace MPS

variable {S : MPS}

/-- The exponents `s_0 < s_1 < ⋯ < s_{t-1}` are positive. -/
def GoodExp (s : ℕ → ℕ) (t : ℕ) : Prop :=
  (∀ j, j < t → 1 ≤ s j) ∧ (∀ i j, i < j → j < t → s i < s j)

/-- Hypothesis (WM): every bounded `E`-measurable function with `E(g|D) = 0` is conditionally
weakly mixing. -/
def WMHyp (S : MPS.{0}) (D E : Factor S) : Prop :=
  ∀ g : S.X → ℝ, Measurable[E.σ] g → (∃ K : ℝ, ∀ x, |g x| ≤ K) →
    (S.m[g | D.σ]) =ᵐ[S.m] 0 → CondWeaklyMixing D g

/-- The star form of the estimate: one factor of conditional expectation zero, all factors
bounded by one. -/
def StarForm (C : CantorData) (t : ℕ) : Prop :=
  ∀ (S : MPS.{0}) [StandardBorelSpace S.X] (D E : Factor S), D.σ ≤ E.σ → WMHyp S D E → ∀ s : ℕ → ℕ, GoodExp s t →
    ∀ f : ℕ → S.X → ℝ, (∀ j, j < t → Measurable[E.σ] (f j)) →
      (∀ j, j < t → ∀ x, |f j x| ≤ 1) → ∀ j₀, j₀ < t → (S.m[f j₀ | D.σ]) =ᵐ[S.m] 0 →
      Tendsto (fun p : ℕ × ℕ => eLpNorm (avgProd C s t f p) 2 S.m) uniformFilter (𝓝 0)

/-- The difference form of the estimate: a product minus the product of the conditional
expectations. -/
def DiffForm (C : CantorData) (t : ℕ) : Prop :=
  ∀ (S : MPS.{0}) [StandardBorelSpace S.X] (D E : Factor S), D.σ ≤ E.σ → WMHyp S D E → ∀ s : ℕ → ℕ, GoodExp s t →
    ∀ f g : ℕ → S.X → ℝ, (∀ j, j < t → Measurable[E.σ] (f j)) →
      (∀ j, j < t → Measurable[D.σ] (g j)) → (∃ B : ℝ, ∀ j, j < t → ∀ x,
        abs (f j x) ≤ B ∧ abs (g j x) ≤ B) → (∀ j, j < t → (S.m[f j | D.σ]) =ᵐ[S.m] g j) →
      Tendsto (fun p : ℕ × ℕ => eLpNorm (avgProd C s t f p - avgProd C s t g p) 2 S.m)
        uniformFilter (𝓝 0)

/-- Scaling a tuple by a constant scales its average by the power of the constant. -/
theorem avgProd_const_mul (C : CantorData) (s : ℕ → ℕ) (t : ℕ) (c : ℝ)
    (φ : ℕ → S.X → ℝ) (p : ℕ × ℕ) :
    avgProd C s t (fun j x => c * φ j x) p = fun x => c ^ t * avgProd C s t φ p x := by
  funext x
  have hn : ∀ n, ∏ j ∈ Finset.range t, c * φ j (S.T^[s j * C.enum n] x)
      = c ^ t * ∏ j ∈ Finset.range t, φ j (S.T^[s j * C.enum n] x) := fun n => by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  simp only [avgProd, hn, ← Finset.mul_sum]
  ring

end MPS

namespace MPS

variable {S : MPS}

/-- **Lemma `lem:wm-main`, the reduction.**  The star form implies the difference form, by
telescoping the difference of products into one term per factor, and rescaling each term so
that its factors lie in `[-1, 1]`. -/
theorem diff_of_star (C : CantorData) (t : ℕ) (hstar : StarForm C t) : DiffForm C t := by
  intro S _ D E hDE hWM s hs f g hfE hgD hB hEg
  obtain ⟨B, hB⟩ := hB
  obtain ⟨B', hB'⟩ : ∃ B' : ℝ, B' = max B 0 := ⟨_, rfl⟩
  obtain ⟨Dc, hDc⟩ : ∃ Dc : ℝ, Dc = 2 * B' + 1 := ⟨_, rfl⟩
  have hB'0 : 0 ≤ B' := by rw [hB']; exact le_max_right _ _
  have hBB' : B ≤ B' := by rw [hB']; exact le_max_left _ _
  have hDc_pos : 0 < Dc := by rw [hDc]; positivity
  have hgE : ∀ j, j < t → Measurable[E.σ] (g j) := fun j hj => (hgD j hj).mono hDE le_rfl
  have hfS : ∀ j, j < t → Measurable (f j) := fun j hj => (hfE j hj).mono E.le le_rfl
  have hgS : ∀ j, j < t → Measurable (g j) := fun j hj => (hgD j hj).mono D.le le_rfl
  -- the modified tuple, normalized to `[-1,1]`
  have hterm : ∀ j₀ ∈ Finset.range t, Tendsto
      (fun p => eLpNorm (avgProd C s t (tupleAt t j₀ f g) p) 2 S.m) uniformFilter (𝓝 0) := by
    intro j₀ hj₀
    have hj : j₀ < t := Finset.mem_range.1 hj₀
    obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → S.X → ℝ, φ = fun j x => tupleAt t j₀ f g j x / Dc := ⟨_, rfl⟩
    have htup : tupleAt t j₀ f g = fun j x => Dc * φ j x := by
      funext j x
      rw [hφ]
      simp only
      rw [mul_div_cancel₀ _ hDc_pos.ne']
    have hmeas : ∀ j, j < t → Measurable[E.σ] (φ j) := by
      intro j hj'
      have : Measurable[E.σ] (tupleAt t j₀ f g j) := by
        unfold tupleAt
        split_ifs with h1 h2
        · exact (hfE j hj').sub (hgE j hj')
        · exact hgE j hj'
        · exact hfE j hj'
      rw [hφ]
      exact this.div_const Dc
    have hbound : ∀ j, j < t → ∀ x, |φ j x| ≤ 1 := by
      intro j hj' x
      have hb : |tupleAt t j₀ f g j x| ≤ Dc := by
        have h3 := hB j hj' x
        unfold tupleAt
        split_ifs with h1 h2
        · have h4 : |f j x - g j x| ≤ |f j x| + |g j x| := abs_sub _ _
          rw [hDc]
          linarith [h3.1, h3.2]
        · rw [hDc]
          linarith [h3.2]
        · rw [hDc]
          linarith [h3.1]
      rw [hφ]
      simp only
      rw [abs_div, abs_of_pos hDc_pos, div_le_one hDc_pos]
      exact hb
    -- the mean-zero condition at `j₀`
    have hfi : Integrable (f j₀) S.m :=
      integrable_of_bdd_const (hfS j₀ hj) (K := B) fun x => (hB j₀ hj x).1
    have hgi : Integrable (g j₀) S.m :=
      integrable_of_bdd_const (hgS j₀ hj) (K := B) fun x => (hB j₀ hj x).2
    have hmean : (S.m[φ j₀ | D.σ]) =ᵐ[S.m] 0 := by
      have hfun : φ j₀ = Dc⁻¹ • (f j₀ - g j₀) := by
        rw [hφ]
        funext x
        simp only [tupleAt, if_true, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [div_eq_inv_mul]
      have hgcond : S.m[g j₀ | D.σ] = g j₀ :=
        condExp_of_stronglyMeasurable D.le (hgD j₀ hj).stronglyMeasurable hgi
      have hsub : S.m[f j₀ - g j₀ | D.σ] =ᵐ[S.m] 0 := by
        filter_upwards [condExp_sub hfi hgi D.σ, hEg j₀ hj] with x h2 h3
        simp [h2, h3, hgcond]
      rw [hfun]
      filter_upwards [condExp_smul Dc⁻¹ (f j₀ - g j₀) D.σ, hsub] with x h1 h2
      simp [h1, h2]
    have hφstar := hstar S D E hDE hWM s hs φ hmeas hbound j₀ hj hmean
    have hpt : ∀ p, avgProd C s t (tupleAt t j₀ f g) p = fun x => Dc ^ t * avgProd C s t φ p x := by
      intro p
      rw [htup, avgProd_const_mul]
    simp only [hpt]
    have hc : ‖(Dc ^ t : ℝ)‖ₑ ≠ ⊤ := enorm_ne_top
    have hscale : ∀ p, eLpNorm (fun x => Dc ^ t * avgProd C s t φ p x) 2 S.m
        = ‖(Dc ^ t : ℝ)‖ₑ * eLpNorm (avgProd C s t φ p) 2 S.m := fun p =>
      eLpNorm_const_smul (Dc ^ t) (avgProd C s t φ p) 2 S.m
    simp only [hscale]
    have := ENNReal.Tendsto.const_mul hφstar (Or.inr hc)
    simpa using this
  -- assemble the sum over `j₀`
  have hsum : ∀ p, avgProd C s t f p - avgProd C s t g p
      = ∑ j₀ ∈ Finset.range t, avgProd C s t (tupleAt t j₀ f g) p :=
    fun p => avgProd_sub_eq_sum C s t f g p
  simp only [hsum]
  have hsumT : Tendsto (fun p => ∑ j₀ ∈ Finset.range t,
      eLpNorm (avgProd C s t (tupleAt t j₀ f g) p) 2 S.m) uniformFilter (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range t) hterm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsumT
    (fun p => zero_le) (fun p => ?_)
  exact eLpNorm_sum_le (μ := S.m) (by norm_num)

end MPS

end CantorSzemeredi

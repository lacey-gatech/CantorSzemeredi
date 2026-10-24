/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.System

/-!
# Conditional Jensen for powers

Blueprint: `blueprint/src/chapter/compact.tex`, Lemma `lem:cond-jensen-power`.

For a measurable `0 ≤ f ≤ 1` and an integer `p`, `E(f^p | D) ≥ E(f | D)^p` almost everywhere.
This is conditional Jensen for the convex function `y ↦ y^p` on `[0,1]`, which is
Mathlib's `ConvexOn.map_condExp_le`.
-/

namespace CantorSzemeredi

open MeasureTheory

namespace MPS

variable {S : MPS}

/-- **Lemma `lem:cond-jensen-power`.**  Conditional Jensen for powers of a `[0,1]`-valued
function. -/
theorem condExp_pow_ge (D : Factor S) {f : S.X → ℝ} (hm : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) (p : ℕ) :
    ∀ᵐ x ∂S.m, (S.m[f | D.σ] x) ^ p ≤ S.m[fun y => f y ^ p | D.σ] x := by
  have hint : Integrable f S.m :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
        exact h1 x)
  have hpow : Integrable (fun y => f y ^ p) S.m :=
    (integrable_const (1 : ℝ)).mono' (hm.pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (h0 x) p)]
        exact pow_le_one₀ (h0 x) (h1 x))
  have hcvx : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun y : ℝ => y ^ p) :=
    (convexOn_pow p).subset Set.Icc_subset_Ici_self (convex_Icc 0 1)
  have hcont : LowerSemicontinuousOn (fun y : ℝ => y ^ p) (Set.Icc (0 : ℝ) 1) :=
    (continuous_pow p).continuousOn.lowerSemicontinuousOn
  have hmem : ∀ᵐ x ∂S.m, f x ∈ Set.Icc (0 : ℝ) 1 :=
    Filter.Eventually.of_forall fun x => ⟨h0 x, h1 x⟩
  have key := hcvx.map_condExp_le D.le hcont hmem isClosed_Icc hint hpow
  filter_upwards [key] with x hx
  exact hx

end MPS

end CantorSzemeredi

/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.System
import CantorSzemeredi.Dynamics.Spectral

/-!
# The Koopman operator

The unitary `f ↦ f ∘ T` on `L²(X; ℂ)` attached to an invertible measure preserving system.
It is what carries the spectral measures of `def:spectral-measure`: the blueprint's `σ_f` is
the spectral measure of the Koopman operator at `f`.

`T` is invertible and measure preserving, so composition with `T` is an isometric
*equivalence* of `L²`, with inverse composition with `T⁻¹`.
-/

namespace CantorSzemeredi

open MeasureTheory

namespace MPS

variable (S : MPS)

/-- **The Koopman operator** `f ↦ f ∘ T` as a unitary of `L²(X; ℂ)`. -/
noncomputable def koopman : Lp ℂ 2 S.m ≃ₗᵢ[ℂ] Lp ℂ 2 S.m where
  toLinearEquiv :=
    { toFun := Lp.compMeasurePreservingₗ ℂ S.T S.measurePreserving
      invFun := Lp.compMeasurePreservingₗ ℂ S.Tinv S.measurePreserving_Tinv
      map_add' := map_add _
      map_smul' := map_smul _
      left_inv := fun g => by
        have h := Lp.compMeasurePreserving_comp_apply (E := ℂ) (p := 2) g
          S.measurePreserving S.measurePreserving_Tinv
        have hid : S.T ∘ S.Tinv = id := funext fun x => S.T_Tinv x
        change (Lp.compMeasurePreserving S.Tinv _) ((Lp.compMeasurePreserving S.T _) g) = g
        rw [← h]
        simp [hid]
      right_inv := fun g => by
        have h := Lp.compMeasurePreserving_comp_apply (E := ℂ) (p := 2) g
          S.measurePreserving_Tinv S.measurePreserving
        have hid : S.Tinv ∘ S.T = id := funext fun x => S.Tinv_T x
        change (Lp.compMeasurePreserving S.T _) ((Lp.compMeasurePreserving S.Tinv _) g) = g
        rw [← h]
        simp [hid] }
  norm_map' g := Lp.norm_compMeasurePreserving g S.measurePreserving

@[simp] theorem koopman_apply (g : Lp ℂ 2 S.m) :
    S.koopman g = Lp.compMeasurePreservingₗ ℂ S.T S.measurePreserving g := rfl

/-- The Koopman operator acts by composition with `T`. -/
theorem coeFn_koopman (g : Lp ℂ 2 S.m) : S.koopman g =ᵐ[S.m] fun x => g (S.T x) :=
  Lp.coeFn_compMeasurePreserving g S.measurePreserving

end MPS

end CantorSzemeredi

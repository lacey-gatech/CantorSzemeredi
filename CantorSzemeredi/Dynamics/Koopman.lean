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

/-- The inverse of the Koopman operator is composition with `T⁻¹`. -/
theorem coeFn_koopman_symm (g : Lp ℂ 2 S.m) :
    S.koopman.symm g =ᵐ[S.m] fun x => g (S.Tinv x) :=
  Lp.coeFn_compMeasurePreserving g S.measurePreserving_Tinv

/-- Powers of the Koopman operator act along the orbit: `Uⁿ g = g ∘ Tⁿ`. -/
theorem coeFn_koopman_zpow (n : ℤ) : ∀ g : Lp ℂ 2 S.m,
    (S.koopman ^ n) g =ᵐ[S.m] fun x => g (S.iter n x) := by
  induction n using Int.induction_on with
  | zero => intro g; filter_upwards with x using by simp
  | succ m ih =>
    intro g
    rw [zpow_add_one S.koopman m]
    have hcomp : (S.koopman ^ (m : ℤ) * S.koopman) g = (S.koopman ^ (m : ℤ)) (S.koopman g) := rfl
    rw [hcomp]
    have h₁ := ih (S.koopman g)
    have h₂ : (fun x => (S.koopman g) (S.iter (m : ℤ) x))
        =ᵐ[S.m] fun x => g (S.T (S.iter (m : ℤ) x)) :=
      (S.measurePreserving_iter (m : ℤ)).quasiMeasurePreserving.ae_eq_comp (S.coeFn_koopman g)
    refine h₁.trans (h₂.trans ?_)
    filter_upwards with x
    have hiter : S.iter ((m : ℤ) + 1) x = S.T (S.iter (m : ℤ) x) := by
      rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring]
      simp only [iter_natCast]
      rw [Function.iterate_succ_apply']
    rw [hiter]
  | pred m ih =>
    intro g
    rw [show (-(m : ℤ) - 1) = (-(m : ℤ)) + (-1) by ring, zpow_add S.koopman, zpow_neg_one]
    have hcomp : (S.koopman ^ (-(m : ℤ)) * S.koopman⁻¹) g
        = (S.koopman ^ (-(m : ℤ))) (S.koopman.symm g) := rfl
    rw [hcomp]
    have h₁ := ih (S.koopman.symm g)
    have h₂ : (fun x => (S.koopman.symm g) (S.iter (-(m : ℤ)) x))
        =ᵐ[S.m] fun x => g (S.Tinv (S.iter (-(m : ℤ)) x)) :=
      (S.measurePreserving_iter (-(m : ℤ))).quasiMeasurePreserving.ae_eq_comp
        (S.coeFn_koopman_symm g)
    refine h₁.trans (h₂.trans ?_)
    filter_upwards with x
    have hiter : S.iter (-(m : ℤ) + -1) x = S.Tinv (S.iter (-(m : ℤ)) x) := by
      rw [show (-(m : ℤ) + -1) = -((m + 1 : ℕ) : ℤ) by push_cast; ring,
        S.iter_neg_natCast, show (-(m : ℤ)) = -((m : ℕ) : ℤ) by push_cast; ring,
        S.iter_neg_natCast, Function.iterate_succ_apply']
    rw [hiter]

end MPS

end CantorSzemeredi

/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.Localize

/-!
# Conditional expectation: bounds, pairing, equivariance

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:condexp-facts`.
-/

namespace CantorSzemeredi

open MeasureTheory Filter

namespace MPS

variable {S : MPS}

/-- **Lemma `lem:condexp-facts`(b), the pairing.**  For a bounded `D`-measurable `v` and an
integrable `u`, `∫ u v = ∫ E(u|D) v`. -/
theorem integral_mul_eq_condExp (D : Factor S) {u v : S.X → ℝ} (hu : Integrable u S.m)
    (hv : StronglyMeasurable[D.σ] v) {C : ℝ} (hvb : ∀ x, |v x| ≤ C) :
    ∫ x, u x * v x ∂S.m = ∫ x, S.m[u | D.σ] x * v x ∂S.m := by
  have hvu : Integrable (v * u) S.m := by
    refine hu.bdd_mul (c := C) (hv.mono D.le).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hvb x
  have hcond := condExp_mul_of_stronglyMeasurable_left hv hvu hu
  calc ∫ x, u x * v x ∂S.m = ∫ x, (v * u) x ∂S.m := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Pi.mul_apply]
        ring
    _ = ∫ x, (S.m[v * u | D.σ]) x ∂S.m := (integral_condExp D.le).symm
    _ = ∫ x, (v * S.m[u | D.σ]) x ∂S.m := integral_congr_ae hcond
    _ = ∫ x, S.m[u | D.σ] x * v x ∂S.m := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Pi.mul_apply]
        ring

/-- **Lemma `lem:condexp-facts`.**  For a `D`-factor and a bounded `u` with `|u| ≤ K`:
(a) `|E(u|D)| ≤ K` almost everywhere;
(b) `∫ u v = ∫ E(u|D) v` for every bounded `D`-measurable `v`;
(c) `E(u ∘ Tⁿ | D) = E(u|D) ∘ Tⁿ` and `‖u ∘ Tⁿ‖_{E|D} = ‖u‖_{E|D} ∘ Tⁿ` almost everywhere. -/
theorem condExp_facts (D : Factor S) {u : S.X → ℝ} {K : ℝ} (hu : Integrable u S.m)
    (hK : ∀ x, |u x| ≤ K) (hu2 : MemLp u 2 S.m) (n : ℕ) :
    (∀ᵐ x ∂S.m, |S.m[u | D.σ] x| ≤ K) ∧
    (∀ (v : S.X → ℝ), StronglyMeasurable[D.σ] v → ∀ C : ℝ, (∀ x, |v x| ≤ C) →
      ∫ x, u x * v x ∂S.m = ∫ x, S.m[u | D.σ] x * v x ∂S.m) ∧
    (S.m[u ∘ S.T^[n] | D.σ] =ᵐ[S.m] (S.m[u | D.σ]) ∘ S.T^[n]) ∧
    (condNorm D (u ∘ S.T^[n]) =ᵐ[S.m] (condNorm D u) ∘ S.T^[n]) :=
  ⟨abs_condExp_le D hu hK, fun v hv C hC => integral_mul_eq_condExp D hu hv hC,
    condExp_comp_iterate D n hu, condNorm_comp_iterate D n hu2⟩

end MPS

end CantorSzemeredi

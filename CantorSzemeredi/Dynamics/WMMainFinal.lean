/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMStar

/-!
# The main estimate of the weakly mixing extensions

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`.  For `t` bounded `E`-measurable
functions `f_j` and integers `0 < s_1 < ⋯ < s_t`, the window averages of
`∏_j T^{s_j k_n} f_j − ∏_j T^{s_j k_n} Exp(f_j | D)` tend to zero in `L²` along the uniform filter.
The conditional expectations are used in their unclipped form; the clipped versions required by
the difference form agree with them almost everywhere, after pulling back along the shifts.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Filter Topology

namespace MPS

/-- **Lemma `lem:wm-main`.**  The main estimate of the weakly mixing extensions. -/
theorem wm_extension_tendsto (C : CantorData) (t : ℕ) {S : MPS.{0}} [StandardBorelSpace S.X]
    (D E : Factor S) (hDE : D.σ ≤ E.σ) (hWM : S.WMHyp D E) (s : ℕ → ℕ) (hs : GoodExp s t)
    (f : ℕ → S.X → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hfE : ∀ j, j < t → Measurable[E.σ] (f j)) (hfb : ∀ j, j < t → ∀ x, |f j x| ≤ B) :
    Tendsto (fun p : ℕ × ℕ => eLpNorm (fun x =>
        (((p.2 - p.1 : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico p.1 p.2,
          (∏ j ∈ range t, f j (S.T^[s j * C.enum n] x)
            - ∏ j ∈ range t, (S.m[f j | D.σ]) (S.T^[s j * C.enum n] x))) 2 S.m)
      uniformFilter (𝓝 0) := by
  -- the clipped conditional expectations, for which the difference form applies
  set g : ℕ → S.X → ℝ := fun j x => max (-B) (min B (S.m[f j | D.σ] x)) with hg
  have hgD : ∀ j, j < t → Measurable[D.σ] (g j) := fun j _ =>
    Measurable.max measurable_const (Measurable.min measurable_const
      stronglyMeasurable_condExp.measurable)
  have hfint : ∀ j, j < t → Integrable (f j) S.m := fun j hj =>
    integrable_of_bdd_const ((hfE j hj).mono E.le le_rfl) (fun x => hfb j hj x)
  have hfmem : ∀ j, j < t → MemLp (f j) 2 S.m := fun j hj =>
    MemLp.of_bound ((hfE j hj).mono E.le le_rfl).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfb j hj x)
  have hEg : ∀ j, j < t → S.m[f j | D.σ] =ᵐ[S.m] g j := fun j hj =>
    (clip_ae_eq (condExp_facts D (hfint j hj) (hfb j hj) (hfmem j hj) 0).1).symm
  have hBds : ∃ B' : ℝ, ∀ j, j < t → ∀ x, |f j x| ≤ B' ∧ |g j x| ≤ B' :=
    ⟨B, fun j hj x => ⟨hfb j hj x, abs_clip_le hB _⟩⟩
  have htend := (diff_of_star C t (starForm_all C t)) S D E hDE hWM s hs f g hfE hgD hBds hEg
  -- the unclipped expressions agree with the clipped ones almost everywhere
  refine htend.congr' (Filter.Eventually.of_forall fun p => ?_)
  apply eLpNorm_congr_ae
  have hpt : ∀ᵐ x ∂S.m, ∀ n ∈ Ico p.1 p.2, ∀ j ∈ range t,
      g j (S.T^[s j * C.enum n] x) = (S.m[f j | D.σ]) (S.T^[s j * C.enum n] x) := by
    refine (Filter.eventually_all_finset _).2 fun n _ => ?_
    refine (Filter.eventually_all_finset _).2 fun j hj => ?_
    have h := (hEg j (Finset.mem_range.1 hj)).symm
    exact (S.measurePreserving_T_iterate _).quasiMeasurePreserving.ae h
  filter_upwards [hpt] with x hx
  simp only [avgProd, Pi.sub_apply]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  exact hx n hn j hj

end MPS

end CantorSzemeredi

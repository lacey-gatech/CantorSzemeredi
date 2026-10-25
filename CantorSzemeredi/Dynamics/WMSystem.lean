/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMPartW

/-!
# Weakly mixing systems

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `cor:wm-system`.  For a weakly mixing system and
bounded measurable `f_1, …, f_t`, along integers `0 < s_1 < ⋯ < s_t`, the uniform averages of
`∏_j T^{s_j k_n} f_j` converge in `L²` to the constant `∏_j ∫ f_j`.  This is the main estimate
`lem:wm-main` for the trivial factor, using `lem:wm-sets-to-functions`.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Filter Topology

namespace MPS

/-- **Corollary `cor:wm-system`.**  For a weakly mixing system `S`, the uniform averages of the
products `∏_j T^{s_j k_n} f_j` tend to `∏_j ∫ f_j` in `L²`. -/
theorem weaklyMixing_tendsto_prod {S : MPS.{0}} [StandardBorelSpace S.X] (hWM : S.WeaklyMixing)
    (C : CantorData) (t : ℕ) (s : ℕ → ℕ) (hs : GoodExp s t) (f : ℕ → S.X → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hfm : ∀ j, j < t → Measurable (f j))
    (hfb : ∀ j, j < t → ∀ x, |f j x| ≤ B) :
    Tendsto (fun p : ℕ × ℕ => eLpNorm (fun x =>
        (((p.2 - p.1 : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico p.1 p.2,
          ∏ j ∈ range t, f j (S.T^[s j * C.enum n] x)
        - ∏ j ∈ range t, ∫ y, f j y ∂S.m) 2 S.m)
      uniformFilter (𝓝 0) := by
  -- the main estimate for the trivial factor and the top factor
  have hE : WeaklyMixingExtension (Factor.trivial S) (Factor.top S) :=
    weaklyMixingExtension_of_weaklyMixing hWM
  have hwm := wm_extension_tendsto C t (Factor.trivial S) (Factor.top S) bot_le
    (wmHyp_of_wmExt hE) s hs f hB (fun j hj => (hfm j hj).mono (Factor.top S).le le_rfl)
    (fun j hj x => hfb j hj x)
  -- the conditional expectations onto the trivial factor are the constant integrals
  have hconst : ∀ j, S.m[f j | (Factor.trivial S).σ] = fun _ => ∫ y, f j y ∂S.m := by
    intro j
    change S.m[f j | ⊥] = _
    rw [condExp_bot' (f j)]
    funext x
    simp
  -- on windows of positive length the average of the constant products is the constant
  have hcongr : ∀ p : ℕ × ℕ, 0 < p.2 - p.1 → ∀ x,
      (((p.2 - p.1 : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico p.1 p.2,
          (∏ j ∈ range t, f j (S.T^[s j * C.enum n] x)
            - ∏ j ∈ range t, (S.m[f j | (Factor.trivial S).σ]) (S.T^[s j * C.enum n] x))
        = (((p.2 - p.1 : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico p.1 p.2,
            ∏ j ∈ range t, f j (S.T^[s j * C.enum n] x)
          - ∏ j ∈ range t, ∫ y, f j y ∂S.m := by
    intro p hp x
    have hsimp : ∀ n, ∏ j ∈ range t, (S.m[f j | (Factor.trivial S).σ]) (S.T^[s j * C.enum n] x)
        = ∏ j ∈ range t, ∫ y, f j y ∂S.m := fun n =>
      Finset.prod_congr rfl fun j _ => by rw [hconst j]
    simp only [hsimp, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hne : ((p.2 - p.1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hp.ne'
    field_simp
  -- transfer the limit to the averages of the products
  refine hwm.congr' ?_
  have hS : {p : ℕ × ℕ | 0 < p.2 - p.1} ∈ uniformFilter :=
    mem_uniformFilter_iff.2 ⟨1, fun M N h => h⟩
  filter_upwards [hS] with p hp
  congr 1
  funext x
  exact hcongr p hp x

end MPS

end CantorSzemeredi

/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.CSZ
import CantorSzemeredi.Dynamics.Unfortunate
import CantorSzemeredi.Dynamics.CondJensenPow

/-!
# The compact-extension theorem: the pointwise estimates

Blueprint: `blueprint/src/chapter/compact.tex`, proof of `thm:compact-extension`.

This file collects the pointwise and almost-everywhere estimates used in the proof:

* the conditional norm is `D`-measurable;
* `E(|w| | D) ≤ ‖w‖_{E|D}` (conditional Jensen for `√`);
* a telescoping bound for products of `[0,1]`-valued functions;
* the lower bound `E(∏_{s≤t} T^{s d} f | D) ≥ E(f | D)^{t+1} - (t+1) ε` on the set where
  each `‖T^{sd} f - f‖_{E|D} < ε`.
-/

namespace CantorSzemeredi

open MeasureTheory Filter

namespace MPS

variable {S : MPS}

/-- The conditional norm is `D`-measurable. -/
theorem measurable_condNorm (D : Factor S) (v : S.X → ℝ) : Measurable[D.σ] (condNorm D v) := by
  unfold condNorm condInner
  exact Real.continuous_sqrt.measurable.comp (stronglyMeasurable_condExp (m := D.σ)).measurable

/-- **`E(|w| | D) ≤ ‖w‖_{E|D}`**, by conditional Jensen for the concave function `√`. -/
theorem condExp_abs_le_condNorm (D : Factor S) {w : S.X → ℝ} (hw : MemLp w 2 S.m) :
    ∀ᵐ x ∂S.m, S.m[fun y => |w y| | D.σ] x ≤ condNorm D w x := by
  have hmm : Integrable (fun y => w y * w y) S.m := hw.integrable_mul hw
  have habs : Integrable (fun y => |w y|) S.m :=
    (hw.integrable (by norm_num : (1 : ENNReal) ≤ 2)).abs
  have key := (Real.strictConcaveOn_sqrt.concaveOn).condExp_map_le D.le
    (Real.continuous_sqrt.continuousOn.upperSemicontinuousOn) (Filter.Eventually.of_forall fun y =>
      mul_self_nonneg (w y)) isClosed_Ici hmm (by
        have heq : ((fun x : ℝ => Real.sqrt x) ∘ fun y => w y * w y) = fun y => |w y| :=
          funext fun y => Real.sqrt_mul_self_eq_abs (w y)
        rw [heq]
        exact habs)
  have heq : ((fun x : ℝ => Real.sqrt x) ∘ fun y => w y * w y) = fun y => |w y| :=
    funext fun y => Real.sqrt_mul_self_eq_abs (w y)
  rw [heq] at key
  filter_upwards [key] with x hx
  exact hx

/-- The telescoping bound for products of `[0,1]`-valued sequences. -/
theorem abs_prod_sub_prod_le_sum (n : ℕ) (x y : ℕ → ℝ) (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1)
    (hy : ∀ s, 0 ≤ y s ∧ y s ≤ 1) :
    |∏ s ∈ Finset.range (n + 1), x s - ∏ s ∈ Finset.range (n + 1), y s|
      ≤ ∑ s ∈ Finset.range (n + 1), |x s - y s| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ x (n + 1), Finset.prod_range_succ y (n + 1),
      Finset.sum_range_succ]
    have hPx0 : 0 ≤ ∏ s ∈ Finset.range (n + 1), x s :=
      Finset.prod_nonneg fun s _ => (hx s).1
    have hPx1 : ∏ s ∈ Finset.range (n + 1), x s ≤ 1 :=
      Finset.prod_le_one₀ (fun s _ => (hx s).1) fun s _ => (hx s).2
    have hPy0 : 0 ≤ ∏ s ∈ Finset.range (n + 1), y s :=
      Finset.prod_nonneg fun s _ => (hy s).1
    have hPy1 : ∏ s ∈ Finset.range (n + 1), y s ≤ 1 :=
      Finset.prod_le_one₀ (fun s _ => (hy s).1) fun s _ => (hy s).2
    have hxs : |x (n + 1)| ≤ 1 := by
      rw [abs_of_nonneg (hx _).1]; exact (hx _).2
    have hys : |∏ s ∈ Finset.range (n + 1), y s| ≤ 1 := by
      rw [abs_of_nonneg hPy0]; exact hPy1
    have hsplit : (∏ s ∈ Finset.range (n + 1), x s) * x (n + 1)
        - (∏ s ∈ Finset.range (n + 1), y s) * y (n + 1)
        = ((∏ s ∈ Finset.range (n + 1), x s) - ∏ s ∈ Finset.range (n + 1), y s) * x (n + 1)
          + (∏ s ∈ Finset.range (n + 1), y s) * (x (n + 1) - y (n + 1)) := by ring
    rw [hsplit]
    calc _ ≤ |((∏ s ∈ Finset.range (n + 1), x s) - ∏ s ∈ Finset.range (n + 1), y s)
            * x (n + 1)| + |(∏ s ∈ Finset.range (n + 1), y s) * (x (n + 1) - y (n + 1))| :=
          abs_add_le _ _
      _ ≤ |(∏ s ∈ Finset.range (n + 1), x s) - ∏ s ∈ Finset.range (n + 1), y s|
            + |x (n + 1) - y (n + 1)| := by
          rw [abs_mul, abs_mul]
          have h1 : |(∏ s ∈ Finset.range (n + 1), x s) - ∏ s ∈ Finset.range (n + 1), y s|
              * |x (n + 1)| ≤ |(∏ s ∈ Finset.range (n + 1), x s) - ∏ s ∈ Finset.range (n + 1), y s| :=
            mul_le_of_le_one_right (abs_nonneg _) hxs
          have h2 : |∏ s ∈ Finset.range (n + 1), y s| * |x (n + 1) - y (n + 1)|
              ≤ |x (n + 1) - y (n + 1)| :=
            mul_le_of_le_one_left (abs_nonneg _) hys
          linarith
      _ ≤ ∑ s ∈ Finset.range (n + 1), |x s - y s| + |x (n + 1) - y (n + 1)| := by
          linarith [ih]

/-- A measurable function with values in `[0,1]` is integrable. -/
theorem integrable_of_unit_bound {g : S.X → ℝ} (hm : Measurable g) (h0 : ∀ x, 0 ≤ g x)
    (h1 : ∀ x, g x ≤ 1) : Integrable g S.m :=
  (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
      exact h1 x)

/-- **Lower bound on a product, on the set where the orbit is close.**  Let `0 ≤ f ≤ 1` be
measurable with `f ∈ L²`, and let `d ∈ ℕ`.  Almost surely, if `‖T^{sd} f - f‖_{E|D} < ε` for
all `s ≤ t`, then `E(∏_{s ≤ t} T^{sd} f | D) ≥ E(f | D)^{t+1} - (t+1) ε`. -/
theorem prod_lower_bound (D : Factor S) {f : S.X → ℝ} (hm : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) (hf : MemLp f 2 S.m) (t d : ℕ) {ε : ℝ} :
    ∀ᵐ x ∂S.m, (∀ s ≤ t, condNorm D (f ∘ S.T^[s * d] - f) x < ε) →
      (S.m[f | D.σ] x) ^ (t + 1) - (t + 1) * ε
        ≤ S.m[fun y => ∏ s ∈ Finset.range (t + 1), f (S.T^[s * d] y) | D.σ] x := by
  set w : ℕ → S.X → ℝ := fun s => f ∘ S.T^[s * d] - f with hw_def
  have hw : ∀ s, MemLp (w s) 2 S.m := fun s =>
    (hf.comp_measurePreserving (S.measurePreserving_T_iterate (s * d))).sub hf
  have habs : ∀ s, Integrable (fun y => |w s y|) S.m := fun s =>
    ((hw s).integrable (by norm_num : (1 : ENNReal) ≤ 2)).abs
  set W : S.X → ℝ := ∑ s ∈ Finset.range (t + 1), (fun y => |w s y|) with hW_def
  have hWint : Integrable W S.m := by
    rw [hW_def, Finset.sum_fn]
    exact integrable_finsetSum _ fun s _ => habs s
  have hpow : Integrable (fun y => f y ^ (t + 1)) S.m :=
    integrable_of_unit_bound (hm.pow_const _) (fun x => pow_nonneg (h0 x) _)
      (fun x => pow_le_one₀ (h0 x) (h1 x))
  have hP : Integrable (fun y => ∏ s ∈ Finset.range (t + 1), f (S.T^[s * d] y)) S.m := by
    refine integrable_of_unit_bound ?_ (fun x => Finset.prod_nonneg fun s _ => h0 _)
      (fun x => Finset.prod_le_one₀ (fun s _ => h0 _) fun s _ => h1 _)
    exact Finset.measurable_prod _ fun s _ => hm.comp (S.measurable_T.iterate _)
  -- The pointwise inequality `f^{t+1} - W ≤ ∏ T^{sd} f`.
  have hpt : (fun y => f y ^ (t + 1) - W y) ≤
      fun y => ∏ s ∈ Finset.range (t + 1), f (S.T^[s * d] y) := by
    intro y
    have hprod := abs_prod_sub_prod_le_sum t (fun s => f (S.T^[s * d] y)) (fun s => f y)
      (fun s => ⟨h0 _, h1 _⟩) (fun s => ⟨h0 y, h1 y⟩)
    rw [Finset.prod_const, Finset.card_range] at hprod
    have hle := (abs_le.1 hprod).1
    have hW : W y = ∑ s ∈ Finset.range (t + 1), |f (S.T^[s * d] y) - f y| := by
      simp [hW_def, Finset.sum_apply, hw_def, Function.comp]
    change f y ^ (t + 1) - W y ≤ ∏ s ∈ Finset.range (t + 1), f (S.T^[s * d] y)
    rw [hW]
    linarith
  have hmono := condExp_mono (m := D.σ) (hpow.sub hWint) hP (Filter.Eventually.of_forall hpt)
  have hlin := condExp_sub hpow hWint D.σ
  have hsum := condExp_finsetSum (m := D.σ) (μ := S.m) (s := Finset.range (t + 1))
    (f := fun s y => |w s y|) (fun s _ => habs s)
  have hpowE := condExp_pow_ge D hm h0 h1 (t + 1)
  have hcomp : ∀ᵐ x ∂S.m, ∀ s, S.m[fun y => |w s y| | D.σ] x ≤ condNorm D (w s) x :=
    ae_all_iff.2 fun s => condExp_abs_le_condNorm D (hw s)
  filter_upwards [hmono, hlin, hsum, hpowE, hcomp] with x hx1 hx2 hx3 hx4 hx5
  intro hgood
  have hW3 : S.m[W | D.σ] x = ∑ s ∈ Finset.range (t + 1), S.m[fun y => |w s y| | D.σ] x := by
    rw [hW_def]
    simpa [Finset.sum_apply] using hx3
  have hsum_le : ∑ s ∈ Finset.range (t + 1), S.m[fun y => |w s y| | D.σ] x
      ≤ ∑ s ∈ Finset.range (t + 1), ε := by
    refine Finset.sum_le_sum fun s hs => le_trans (hx5 s) (le_of_lt ?_)
    exact hgood s (by have := Finset.mem_range.1 hs; omega)
  have hconst : ∑ s ∈ Finset.range (t + 1), ε = (t + 1) * ε := by simp
  have hlin' : S.m[fun y => f y ^ (t + 1) - W y | D.σ] x
      = S.m[fun y => f y ^ (t + 1) | D.σ] x - S.m[W | D.σ] x := hx2
  have hpt' : S.m[fun y => f y ^ (t + 1) - W y | D.σ] x
      ≤ S.m[fun y => ∏ s ∈ Finset.range (t + 1), f (S.T^[s * d] y) | D.σ] x := hx1
  linarith

/-- **Integral over a good set.**  On a `D`-set `I` where `E(f|D) ≥ c` and on the set where the
orbit `T^{sd} f` is `ε`-close to `f` in conditional norm, the integral of the product is at least
`(c^{t+1} - (t+1) ε)` times the measure of that set. -/
theorem integral_prod_ge_of_mem (D : Factor S) {f : S.X → ℝ} (hm : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) (hf : MemLp f 2 S.m) (t d : ℕ) {ε c : ℝ}
    {I : Set S.X} (hI : MeasurableSet[D.σ] I) (hIc : ∀ x ∈ I, c ≤ S.m[f | D.σ] x)
    (hc : 0 ≤ c) :
    (c ^ (t + 1) - (t + 1) * ε) *
        (S.m (I ∩ {x | ∀ s ≤ t, condNorm D (f ∘ S.T^[s * d] - f) x < ε})).toReal
      ≤ ∫ x, ∏ s ∈ Finset.range (t + 1), f (S.T^[s * d] x) ∂S.m := by
  set W : Set S.X := {x | ∀ s ≤ t, condNorm D (f ∘ S.T^[s * d] - f) x < ε} with hW_def
  have hWD : MeasurableSet[D.σ] W := by
    have : W = ⋂ s ∈ Finset.range (t + 1),
        {x | condNorm D (f ∘ S.T^[s * d] - f) x < ε} := by
      ext x
      simp [hW_def]
    rw [this]
    refine Finset.measurableSet_biInter _ fun s _ => ?_
    exact measurableSet_lt (measurable_condNorm D _) measurable_const
  set J : Set S.X := I ∩ W with hJ_def
  have hJD : MeasurableSet[D.σ] J := hI.inter hWD
  have hP : Integrable (fun y => ∏ s ∈ Finset.range (t + 1), f (S.T^[s * d] y)) S.m :=
    integrable_of_unit_bound (Finset.measurable_prod _ fun s _ => hm.comp (S.measurable_T.iterate _))
      (fun x => Finset.prod_nonneg fun s _ => h0 _)
      (fun x => Finset.prod_le_one₀ (fun s _ => h0 _) fun s _ => h1 _)
  have hlow : ∀ᵐ x ∂S.m, x ∈ J →
      c ^ (t + 1) - (t + 1) * ε ≤ S.m[fun y => ∏ s ∈ Finset.range (t + 1), f (S.T^[s * d] y) | D.σ] x := by
    filter_upwards [prod_lower_bound D hm h0 h1 hf t d] with x hx hxJ
    have hpow : c ^ (t + 1) ≤ (S.m[f | D.σ] x) ^ (t + 1) :=
      pow_le_pow_left₀ hc (hIc x hxJ.1) _
    have := hx hxJ.2
    linarith
  have hmeasJ : MeasurableSet J := D.le _ hJD
  have hint1 : ∫ x in J, c ^ (t + 1) - (t + 1) * ε ∂S.m
      ≤ ∫ x in J, S.m[fun y => ∏ s ∈ Finset.range (t + 1), f (S.T^[s * d] y) | D.σ] x ∂S.m := by
    refine setIntegral_mono_ae_restrict (integrableOn_const (measure_ne_top S.m J))
      integrable_condExp.integrableOn ?_
    exact (ae_restrict_iff' hmeasJ).2 hlow
  have hPJ : ∫ x in J, S.m[fun y => ∏ s ∈ Finset.range (t + 1), f (S.T^[s * d] y) | D.σ] x ∂S.m
      = ∫ x in J, ∏ s ∈ Finset.range (t + 1), f (S.T^[s * d] x) ∂S.m :=
    setIntegral_condExp D.le hP hJD
  have hle : ∫ x in J, ∏ s ∈ Finset.range (t + 1), f (S.T^[s * d] x) ∂S.m
      ≤ ∫ x, ∏ s ∈ Finset.range (t + 1), f (S.T^[s * d] x) ∂S.m :=
    setIntegral_le_integral hP (Filter.Eventually.of_forall fun x =>
      Finset.prod_nonneg fun s _ => h0 _)
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at hint1
  rw [hPJ] at hint1
  linarith

/-- **Choice of a translate with large mass.**  If almost every point of `I` lies in some
`W a` with `a ∈ F`, then some `a ∈ F` has `m(I ∩ W a) ≥ m(I) / |F|`. -/
theorem exists_mass_index {I : Set S.X} {F : Finset ℕ}
    (hF : F.Nonempty) {W : ℕ → Set S.X} (hcov : ∀ᵐ x ∂S.m, x ∈ I → ∃ a ∈ F, x ∈ W a) :
    ∃ a ∈ F, (S.m I).toReal / F.card ≤ (S.m (I ∩ W a)).toReal := by
  have hsub : I ≤ᵐ[S.m] ⋃ a ∈ F, I ∩ W a := by
    filter_upwards [hcov] with x hx hxI
    obtain ⟨a, ha, hxa⟩ := hx hxI
    exact Set.mem_biUnion ha ⟨hxI, hxa⟩
  have h1 : S.m I ≤ ∑ a ∈ F, S.m (I ∩ W a) :=
    (measure_mono_ae hsub).trans (measure_biUnion_finset_le _ _)
  have h2 : (S.m I).toReal ≤ ∑ a ∈ F, (S.m (I ∩ W a)).toReal := by
    rw [← ENNReal.toReal_sum fun a _ => measure_ne_top _ _]
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun a _ => measure_ne_top _ _) h1
  have hcard : (F.card : ℝ) ≠ 0 := by
    have := Finset.card_pos.2 hF
    positivity
  have h3 : ∑ a ∈ F, (S.m I).toReal / F.card = (S.m I).toReal := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  obtain ⟨a, ha, hle⟩ := Finset.exists_le_of_sum_le (f := fun _ => (S.m I).toReal / F.card)
    (g := fun a => (S.m (I ∩ W a)).toReal) hF (by rw [h3]; exact h2)
  exact ⟨a, ha, hle⟩

/-- **Density of the good averaging parameters.**  If the uniform `liminf` of `a` is `c0 > 0`,
then the set of `u ≥ 1` with `a u > c0/2` has lower uniform density at least `c0/2`. -/
theorem density_of_uniformLiminf {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    {c0 θ : ℝ} (hc0 : uniformLiminf a = c0) (hc0pos : 0 < c0) (hθ : 0 < θ) :
    ∃ L : ℕ, ∀ M N : ℕ, L ≤ N - M →
      c0 / 2 - θ ≤ (((Finset.Ico M N).filter (fun u => 1 ≤ u ∧ c0 / 2 < a u)).card : ℝ)
        / ((N - M : ℕ) : ℝ) := by
  have hliminf : uniformLiminf a = Filter.liminf (fun p : ℕ × ℕ => uniformAvg a p.1 p.2)
      uniformFilter := rfl
  have hev : {p : ℕ × ℕ | c0 - θ / 2 < uniformAvg a p.1 p.2} ∈ uniformFilter := by
    apply Filter.eventually_lt_of_lt_liminf
    · rw [← hliminf, hc0]
      linarith
    · exact Filter.isBoundedUnder_of ⟨0, fun p => uniformAvg_nonneg ha0 _ _⟩
  obtain ⟨L, hL⟩ := mem_uniformFilter_iff.1 hev
  set K : ℕ := ⌈2 / θ⌉₊ with hK
  refine ⟨max (max L K) 1, fun M N hW => ?_⟩
  have hWL : L ≤ N - M := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hW)
  have hWK : 2 / θ ≤ ((N - M : ℕ) : ℝ) := by
    have h1 : K ≤ N - M := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hW)
    have h2 : (K : ℝ) ≤ ((N - M : ℕ) : ℝ) := by exact_mod_cast h1
    exact le_trans (Nat.le_ceil _) h2
  have hW1 : 1 ≤ N - M := le_trans (le_max_right _ _) hW
  have hWpos : (0 : ℝ) < ((N - M : ℕ) : ℝ) := by exact_mod_cast hW1
  have havg : c0 - θ / 2 < uniformAvg a M N := hL M N hWL
  unfold uniformAvg at havg
  rw [lt_div_iff₀ hWpos] at havg
  -- Pointwise domination of `a` by the indicator of the good set, `c0/2`, and the point `0`.
  have hterm : ∀ n ∈ Finset.Ico M N, a n ≤
      (if (1 ≤ n ∧ c0 / 2 < a n) then 1 else 0) + c0 / 2 + (if n = 0 then 1 else 0) := by
    intro n _
    have hc0h : 0 ≤ c0 / 2 := by linarith
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hc : ¬ (1 ≤ 0 ∧ c0 / 2 < a 0) := fun h => absurd h.1 (by norm_num)
      simp only [hc, if_false, if_true]
      linarith [ha1 0]
    · have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.1 hn
      simp only [hn0, if_false, add_zero]
      by_cases hB : c0 / 2 < a n
      · have hc : 1 ≤ n ∧ c0 / 2 < a n := ⟨hn, hB⟩
        simp only [hc, and_self, if_true]
        linarith [ha1 n]
      · have hc : ¬ (1 ≤ n ∧ c0 / 2 < a n) := fun h => hB h.2
        simp only [hc, if_false]
        linarith [not_lt.1 hB]
  have hz : ∑ n ∈ Finset.Ico M N, (if n = 0 then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  have hsum : ∑ n ∈ Finset.Ico M N, a n
      ≤ (((Finset.Ico M N).filter (fun u => 1 ≤ u ∧ c0 / 2 < a u)).card : ℝ)
        + ((N - M : ℕ) : ℝ) * (c0 / 2) + 1 := by
    calc ∑ n ∈ Finset.Ico M N, a n
        ≤ ∑ n ∈ Finset.Ico M N, ((if (1 ≤ n ∧ c0 / 2 < a n) then (1 : ℝ) else 0)
            + c0 / 2 + (if n = 0 then (1 : ℝ) else 0)) := Finset.sum_le_sum hterm
      _ = (((Finset.Ico M N).filter (fun u => 1 ≤ u ∧ c0 / 2 < a u)).card : ℝ)
            + ((N - M : ℕ) : ℝ) * (c0 / 2)
            + ∑ n ∈ Finset.Ico M N, (if n = 0 then (1 : ℝ) else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_boole,
            Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ _ := by linarith
  have hθW : 2 ≤ ((N - M : ℕ) : ℝ) * θ := (div_le_iff₀ hθ).1 hWK
  rw [le_div_iff₀ hWpos]
  linarith

end MPS

/-- A uniform average of a sequence with values in `[0,1]` is at most `1`. -/
theorem uniformAvg_le_one' {a : ℕ → ℝ} (ha1 : ∀ n, a n ≤ 1) (M N : ℕ) :
    uniformAvg a M N ≤ 1 := by
  unfold uniformAvg
  rcases Nat.eq_zero_or_pos (N - M) with h | h
  · simp [h]
  · have hpos : (0 : ℝ) < ((N - M : ℕ) : ℝ) := by exact_mod_cast h
    rw [div_le_one hpos]
    calc ∑ n ∈ Finset.Ico M N, a n ≤ ∑ n ∈ Finset.Ico M N, (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => ha1 n
      _ = ((N - M : ℕ) : ℝ) := by simp

/-- **Block sums.**  If each block `[δ u, δ(u+1))` of indices contains a point `v u` at which the
sequence is at least `c2`, then a window `[M, N)` contains at least `c2 · #{u ∈ [M/δ+1, N/δ) : B u}`
of the mass of the sequence. -/
theorem sum_ge_of_blocks {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) {δ : ℕ} (hδ : 1 ≤ δ)
    {B : ℕ → Prop} [DecidablePred B] {v : ℕ → ℕ}
    (hv : ∀ u, B u → δ * u ≤ v u ∧ v u < δ * (u + 1)) {c2 : ℝ}
    (hc2 : ∀ u, B u → c2 ≤ a (v u)) (M N : ℕ) :
    c2 * (((Finset.Ico (M / δ + 1) (N / δ)).filter B).card : ℝ)
      ≤ ∑ n ∈ Finset.Ico M N, a n := by
  set U := (Finset.Ico (M / δ + 1) (N / δ)).filter B with hU
  have hδpos : 0 < δ := hδ
  have hmemU : ∀ u ∈ U, v u ∈ Finset.Ico M N := by
    intro u hu
    rw [hU, Finset.mem_filter, Finset.mem_Ico] at hu
    obtain ⟨⟨h1, h2⟩, hB⟩ := hu
    obtain ⟨hv1, hv2⟩ := hv u hB
    have hM : M < δ * (M / δ + 1) := Nat.lt_mul_div_succ M hδpos
    have hN : δ * (N / δ) ≤ N := Nat.mul_div_le N δ
    have hδu : δ * (M / δ + 1) ≤ δ * u := Nat.mul_le_mul_left δ h1
    have hδu2 : δ * (u + 1) ≤ δ * (N / δ) := Nat.mul_le_mul_left δ (Nat.succ_le_of_lt h2)
    rw [Finset.mem_Ico]
    constructor
    · linarith
    · linarith
  have hinj : Set.InjOn v ↑U := by
    have key : ∀ w ∈ U, w = v w / δ := by
      intro w hw
      obtain ⟨hv1, hv2⟩ := hv w (Finset.mem_filter.1 hw).2
      have hv1' : w * δ ≤ v w := by rw [mul_comm]; exact hv1
      have hv2' : v w < (w + 1) * δ := by rw [mul_comm]; exact hv2
      exact (Nat.div_eq_of_lt_le hv1' hv2').symm
    intro u hu u' hu' huv
    calc u = v u / δ := key u hu
      _ = v u' / δ := by rw [huv]
      _ = u' := (key u' hu').symm
  calc c2 * (U.card : ℝ) = ∑ u ∈ U, c2 := by simp [mul_comm]
    _ ≤ ∑ u ∈ U, a (v u) := Finset.sum_le_sum fun u hu => hc2 u (Finset.mem_filter.1 hu).2
    _ = ∑ n ∈ U.image v, a n := (Finset.sum_image hinj).symm
    _ ≤ ∑ n ∈ Finset.Ico M N, a n := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => ha0 n
      intro n hn
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hn
      exact hmemU u hu

/-- **Uniform liminf from blocks.**  Suppose the sequence `a` is in `[0,1]`, the blocks
`[δ u, δ(u+1))` each contain an index `v u` at which `a ≥ c2 ≥ 0` for every `u ∈ B`, and the set
`B` has lower uniform density at least `κ > 0`.  Then the uniform `liminf` of `a` is at least
`c2 κ / δ`. -/
theorem uniformLiminf_ge_of_blocks {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    {δ : ℕ} (hδ : 1 ≤ δ) {B : ℕ → Prop} [DecidablePred B] {κ : ℝ} (hκ : 0 < κ)
    (hB : ∀ θ : ℝ, 0 < θ → ∃ L : ℕ, ∀ M N : ℕ, L ≤ N - M →
      κ - θ ≤ (((Finset.Ico M N).filter B).card : ℝ) / ((N - M : ℕ) : ℝ))
    {v : ℕ → ℕ} (hv : ∀ u, B u → δ * u ≤ v u ∧ v u < δ * (u + 1))
    {c2 : ℝ} (hc20 : 0 ≤ c2) (hc2 : ∀ u, B u → c2 ≤ a (v u)) :
    c2 * κ / δ ≤ uniformLiminf a := by
  have hliminf : uniformLiminf a = Filter.liminf (fun p : ℕ × ℕ => uniformAvg a p.1 p.2)
      uniformFilter := rfl
  have hcb : Filter.IsBoundedUnder (· ≤ ·) uniformFilter
      (fun p : ℕ × ℕ => uniformAvg a p.1 p.2) :=
    Filter.isBoundedUnder_of ⟨1, fun p => uniformAvg_le_one' ha1 p.1 p.2⟩
  have hδR : (0 : ℝ) < δ := by exact_mod_cast (show 0 < δ by omega)
  rw [hliminf]
  refine le_of_forall_sub_le fun ε hε => ?_
  set θ : ℝ := min (κ / 2) (ε * δ / (2 * (c2 + 1))) with hθ_def
  have hθpos : 0 < θ := lt_min (by linarith) (by positivity)
  have hθκ : θ ≤ κ / 2 := min_le_left _ _
  have hθε : θ ≤ ε * δ / (2 * (c2 + 1)) := min_le_right _ _
  obtain ⟨L, hL⟩ := hB θ hθpos
  set K : ℕ := ⌈4 * c2 * κ / ε⌉₊ with hK
  refine Filter.le_liminf_of_le hcb.isCoboundedUnder_ge ?_
  refine mem_uniformFilter_iff.2 ⟨δ * (L + 2) + K + 1, fun M N hW => ?_⟩
  show c2 * κ / δ - ε ≤ uniformAvg a M N
  have hW1 : δ * (L + 2) ≤ N - M :=
    le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) hW)
  have hK1 : K ≤ N - M :=
    le_trans (le_trans (Nat.le_add_left K _) (Nat.le_add_right _ _)) hW
  have hW0 : 0 < N - M := lt_of_lt_of_le (Nat.succ_pos _) hW
  have hWpos : (0 : ℝ) < ((N - M : ℕ) : ℝ) := by exact_mod_cast hW0
  have hMN : M ≤ N := by omega
  -- the index window `[M/δ+1, N/δ)`
  have hLW : (L + 2) ≤ (N - M) / δ := (Nat.le_div_iff_mul_le (by omega)).2 (by
    rw [mul_comm]; exact hW1)
  have hsplit : M / δ + (N - M) / δ ≤ N / δ := by
    have := Nat.add_div_le_add_div M (N - M) δ
    rwa [Nat.add_sub_cancel' hMN] at this
  have hQP : L ≤ N / δ - (M / δ + 1) := by omega
  -- the length of the window is at least `W/δ - 2`, as real numbers
  set len : ℕ := N / δ - (M / δ + 1) with hlen_def
  have hlenR : ((len : ℕ) : ℝ) = ((N / δ : ℕ) : ℝ) - ((M / δ : ℕ) : ℝ) - 1 := by
    rw [hlen_def, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    ring
  have hN' : (N : ℝ) < (δ : ℝ) * ((N / δ : ℕ) : ℝ) + δ := by
    have h : N < δ * (N / δ) + δ := by
      have := Nat.div_add_mod N δ
      have := Nat.mod_lt N (show δ > 0 by omega)
      omega
    exact_mod_cast h
  have hM' : (δ : ℝ) * ((M / δ : ℕ) : ℝ) ≤ M := by
    exact_mod_cast Nat.mul_div_le M δ
  have hWR : ((N - M : ℕ) : ℝ) = (N : ℝ) - M := by
    rw [Nat.cast_sub hMN]
  have hlenlow : ((N - M : ℕ) : ℝ) / δ - 2 ≤ (len : ℝ) := by
    have hlt : ((N - M : ℕ) : ℝ) < (δ : ℝ) * (((N / δ : ℕ) : ℝ) - ((M / δ : ℕ) : ℝ) + 1) := by
      rw [hWR]
      nlinarith
    have hdiv : ((N - M : ℕ) : ℝ) / δ < ((N / δ : ℕ) : ℝ) - ((M / δ : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hδR]
      linarith
    rw [hlenR]
    linarith
  -- the count of good indices in the window, and the mass in the window
  have hcount : κ - θ ≤ ((((Finset.Ico (M / δ + 1) (N / δ)).filter B).card : ℕ) : ℝ) / (len : ℝ) :=
    hL (M / δ + 1) (N / δ) hQP
  have hlenpos : (0 : ℝ) < (len : ℝ) := by
    have : (L : ℝ) + 1 ≤ (len : ℝ) := by
      have : L + 1 ≤ len := by omega
      exact_mod_cast this
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith
  have hcountR : (κ - θ) * (len : ℝ)
      ≤ (((Finset.Ico (M / δ + 1) (N / δ)).filter B).card : ℝ) := by
    rw [le_div_iff₀ hlenpos] at hcount
    exact hcount
  have hmass := sum_ge_of_blocks ha0 hδ hv hc2 M N
  -- the constants: `θ` is small, and `W` is large
  have hc2θ : c2 * θ ≤ ε * δ / 2 := by
    have h1 : c2 * θ ≤ (c2 + 1) * θ := by nlinarith
    have h2 : (c2 + 1) * θ ≤ (c2 + 1) * (ε * δ / (2 * (c2 + 1))) :=
      mul_le_mul_of_nonneg_left hθε (by linarith)
    have h3 : (c2 + 1) * (ε * δ / (2 * (c2 + 1))) = ε * δ / 2 := by
      field_simp
    linarith
  have hF1 : c2 * θ / δ ≤ ε / 2 := by
    rw [div_le_iff₀ hδR]
    linarith
  have hF2 : 4 * c2 * κ ≤ ε * ((N - M : ℕ) : ℝ) := by
    have h1 : 4 * c2 * κ / ε ≤ (K : ℝ) := Nat.le_ceil _
    have h2 : (K : ℝ) ≤ ((N - M : ℕ) : ℝ) := by exact_mod_cast hK1
    have h3 : 4 * c2 * κ / ε ≤ ((N - M : ℕ) : ℝ) := le_trans h1 h2
    rw [div_le_iff₀ hε] at h3
    linarith
  have hκθ : 0 ≤ κ - θ := by linarith
  -- assemble
  have hsum_lower : c2 * (κ - θ) * (((N - M : ℕ) : ℝ) / δ - 2) ≤ ∑ n ∈ Finset.Ico M N, a n := by
    have e1 : c2 * ((κ - θ) * (len : ℝ))
        ≤ c2 * (((Finset.Ico (M / δ + 1) (N / δ)).filter B).card : ℝ) :=
      mul_le_mul_of_nonneg_left hcountR hc20
    have e2 : c2 * (κ - θ) * (((N - M : ℕ) : ℝ) / δ - 2) ≤ c2 * (κ - θ) * (len : ℝ) :=
      mul_le_mul_of_nonneg_left hlenlow (mul_nonneg hc20 hκθ)
    have e3 : c2 * ((κ - θ) * (len : ℝ)) = c2 * (κ - θ) * (len : ℝ) := by ring
    linarith
  rw [uniformAvg, le_div_iff₀ hWpos]
  have hF1W := mul_le_mul_of_nonneg_right hF1 hWpos.le
  have hc2θ0 : 0 ≤ c2 * θ := mul_nonneg hc20 hθpos.le
  have hexp : c2 * (κ - θ) * (((N - M : ℕ) : ℝ) / δ - 2)
      = c2 * κ / δ * ((N - M : ℕ) : ℝ) - c2 * θ / δ * ((N - M : ℕ) : ℝ)
        - 2 * c2 * κ + 2 * (c2 * θ) := by
    field_simp
    ring
  nlinarith [hsum_lower, hF1W, hF2, hexp, hc2θ0]
end CantorSzemeredi

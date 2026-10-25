/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMSetsToFunctions
import CantorSzemeredi.Dynamics.CSZ
import CantorSzemeredi.Dynamics.CompactExtensionCSZ
import CantorSzemeredi.Dynamics.WMLimit
import CantorSzemeredi.Dynamics.WMMainFinal

/-!
# Part (W) of the extension principles

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-extension`.  If `D` is CSZ and `E` is a
weakly mixing extension of `D`, then `E` is CSZ.  The proof compares the uniform averages of the
products `∏ T^{s d} 1_A` with those of `∏ T^{s d} g`, where `g` is a clipped conditional expectation
of `1_A`, using the main estimate `lem:wm-main`; the positivity of the uniform `liminf` of the
functional sequence is transferred to the indicator sequence.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Filter Topology

/-- The uniform averages of a sequence with values in `[0,1]` lie in `[0,1]`. -/
theorem uniformAvg_mem (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n ∧ x n ≤ 1) (M N : ℕ) :
    0 ≤ uniformAvg x M N ∧ uniformAvg x M N ≤ 1 := by
  constructor
  · unfold uniformAvg
    exact div_nonneg (Finset.sum_nonneg fun n _ => (hx n).1) (Nat.cast_nonneg _)
  · unfold uniformAvg
    rcases Nat.eq_zero_or_pos (N - M) with h | h
    · simp [h]
    · have hpos : (0 : ℝ) < ((N - M : ℕ) : ℝ) := by exact_mod_cast h
      rw [div_le_one hpos]
      calc ∑ n ∈ Finset.Ico M N, x n ≤ ∑ n ∈ Finset.Ico M N, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => (hx n).2
        _ = ((N - M : ℕ) : ℝ) := by simp

/-- **Transfer of positivity.**  If two sequences in `[0,1]` have uniform averages whose difference
tends to zero along the uniform filter, and the uniform `liminf` of the second is positive, so is
the uniform `liminf` of the first. -/
theorem uniformLiminf_pos_of_sub_tendsto (a e : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n ∧ a n ≤ 1)
    (he : ∀ n, 0 ≤ e n ∧ e n ≤ 1)
    (hd : Tendsto (fun p : ℕ × ℕ => uniformAvg a p.1 p.2 - uniformAvg e p.1 p.2) uniformFilter
      (𝓝 0))
    (hpos : 0 < uniformLiminf e) : 0 < uniformLiminf a := by
  have hL := hpos
  unfold uniformLiminf at hL ⊢
  set L := Filter.liminf (fun p : ℕ × ℕ => uniformAvg e p.1 p.2) uniformFilter with hLdef
  have hbdd_e : uniformFilter.IsBoundedUnder (· ≥ ·)
      (fun p : ℕ × ℕ => uniformAvg e p.1 p.2) :=
    isBoundedUnder_of ⟨0, fun p => (uniformAvg_mem e he _ _).1⟩
  have hev_e : ∀ᶠ p in uniformFilter, L / 2 < uniformAvg e p.1 p.2 :=
    eventually_lt_of_lt_liminf (by linarith) hbdd_e
  have hdist := Metric.tendsto_nhds.1 hd (L / 4) (by positivity)
  have hev_a : ∀ᶠ p in uniformFilter, L / 4 < uniformAvg a p.1 p.2 := by
    filter_upwards [hev_e, hdist] with p h1 h2
    rw [Real.dist_eq, sub_zero] at h2
    have := (abs_lt.1 h2).1
    linarith
  have hle : L / 4 ≤ Filter.liminf (fun p : ℕ × ℕ => uniformAvg a p.1 p.2) uniformFilter :=
    Filter.le_liminf_of_le
      (isCoboundedUnder_ge_of_le uniformFilter (x := 1) fun p => (uniformAvg_mem a ha _ _).2)
      (hev_a.mono fun p hp => hp.le)
  linarith

namespace MPS

/-- A bounded `E`-measurable function is in the module `L²(E)` over `D`. -/
theorem memModule_of_bdd {S : MPS.{0}} (D E : Factor S) {f : S.X → ℝ}
    (hm : Measurable[E.σ] f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) : MemModule D E f := by
  have hmA : Measurable f := hm.mono E.le le_rfl
  refine ⟨hm.aestronglyMeasurable, ?_, ?_⟩
  · exact MemLp.of_bound hmA.aestronglyMeasurable |K| (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact le_trans (hK x) (le_abs_self K))
  · refine ⟨Real.sqrt (|K| ^ 2), ?_⟩
    have hbd : ∀ x, |f x * f x| ≤ |K| ^ 2 := fun x => by
      rw [abs_mul, sq]
      exact mul_le_mul (le_trans (hK x) (le_abs_self K)) (le_trans (hK x) (le_abs_self K))
        (abs_nonneg _) (abs_nonneg _)
    have hint : Integrable (fun x => f x * f x) S.m :=
      integrable_of_bdd_const (hmA.mul hmA) (K := |K| ^ 2) hbd
    have hcond := abs_condExp_le D hint (K := |K| ^ 2) hbd
    filter_upwards [hcond] with x hx
    unfold condNorm
    apply Real.sqrt_le_sqrt
    calc condInner D f f x ≤ |condInner D f f x| := le_abs_self _
      _ ≤ |K| ^ 2 := hx

/-- A weakly mixing extension satisfies the hypothesis `(WM)` of the main estimate. -/
theorem wmHyp_of_wmExt {S : MPS.{0}} {D E : Factor S} (h : WeaklyMixingExtension D E) :
    S.WMHyp D E := by
  intro g hg hK hmean
  obtain ⟨K, hK⟩ := hK
  exact h g (memModule_of_bdd D E hg hK) hmean

end MPS

namespace MPS

/-- The clipped conditional expectation: a version of `Exp(ind | D)` with values in `[0,1]`
everywhere. -/
noncomputable def clipCond {S : MPS.{0}} (D : Factor S) (ind : S.X → ℝ) : S.X → ℝ :=
  fun x => max 0 (min 1 (S.m[ind | D.σ] x))

theorem clipCond_meas {S : MPS.{0}} (D : Factor S) (ind : S.X → ℝ) :
    Measurable[D.σ] (clipCond D ind) :=
  Measurable.max measurable_const (Measurable.min measurable_const
    stronglyMeasurable_condExp.measurable)

theorem clipCond_mem {S : MPS.{0}} (D : Factor S) (ind : S.X → ℝ) (x : S.X) :
    0 ≤ clipCond D ind x ∧ clipCond D ind x ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- For an indicator-type function with values in `[0,1]`, the clipped conditional expectation is
almost everywhere the conditional expectation. -/
theorem clipCond_ae {S : MPS.{0}} (D : Factor S) {ind : S.X → ℝ} (hm : Measurable ind)
    (h0 : ∀ x, 0 ≤ ind x) (h1 : ∀ x, |ind x| ≤ 1) :
    clipCond D ind =ᵐ[S.m] S.m[ind | D.σ] := by
  have hnn : 0 ≤ᵐ[S.m] S.m[ind | D.σ] :=
    condExp_nonneg (Filter.Eventually.of_forall h0)
  filter_upwards [hnn, abs_condExp_ae_le D hm h1] with x hx1 hx2
  unfold clipCond
  rw [min_eq_right (abs_le.1 hx2).2, max_eq_right (show (0:ℝ) ≤ S.m[ind | D.σ] x from hx1)]

/-- **Pairing with the clipped expectation.**  For a bounded `D`-measurable `v`, the integral of
`ind · v` equals the integral of `clipCond · v`. -/
theorem integral_ind_mul_eq_clip {S : MPS.{0}} (D : Factor S) {A : Set S.X}
    (hA : MeasurableSet A) {v : S.X → ℝ} (hv : Measurable[D.σ] v) {K : ℝ}
    (hvb : ∀ x, |v x| ≤ K) :
    ∫ x, A.indicator (1 : S.X → ℝ) x * v x ∂S.m
      = ∫ x, clipCond D (A.indicator 1) x * v x ∂S.m := by
  have hind : Measurable (A.indicator (1 : S.X → ℝ)) :=
    measurable_const.indicator hA
  have hindb : ∀ x, |A.indicator (1 : S.X → ℝ) x| ≤ 1 := fun x => by
    by_cases hx : x ∈ A
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hindnn : ∀ x, 0 ≤ A.indicator (1 : S.X → ℝ) x := fun x => by
    by_cases hx : x ∈ A
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  obtain ⟨hint, hmem⟩ := integrable_memLp_of_bound hind hindb
  have hcf := (condExp_facts D hint hindb hmem 0).2.1 v hv.stronglyMeasurable K hvb
  rw [hcf]
  refine integral_congr_ae ?_
  filter_upwards [clipCond_ae D hind hindnn hindb] with x hx
  rw [hx]

/-- The product over `s ≤ t` splits into the factor at `0` and the shifted factors. -/
theorem integral_prod_range_succ' {S : MPS.{0}} (h : S.X → ℝ) (t d : ℕ) :
    ∫ x, ∏ s ∈ range (t + 1), h (S.T^[s * d] x) ∂S.m
      = ∫ x, h x * ∏ j ∈ range t, h (S.T^[(j + 1) * d] x) ∂S.m := by
  congr 1
  funext x
  rw [Finset.prod_range_succ', mul_comm]
  simp

/-- A product of values in `[0,1]` lies in `[0,1]`. -/
theorem prod_mem_unit {S : MPS.{0}} (h : S.X → ℝ) (h0 : ∀ x, 0 ≤ h x) (h1 : ∀ x, h x ≤ 1)
    (t d : ℕ) (x : S.X) :
    0 ≤ ∏ s ∈ range (t + 1), h (S.T^[s * d] x) ∧ ∏ s ∈ range (t + 1), h (S.T^[s * d] x) ≤ 1 :=
  ⟨Finset.prod_nonneg fun s _ => h0 _,
    Finset.prod_le_one₀ (fun s _ => h0 _) fun s _ => h1 _⟩

/-- An integral of a function with values in `[0,1]` lies in `[0,1]`. -/
theorem integral_mem_unit {S : MPS.{0}} (F : S.X → ℝ) (h0 : ∀ x, 0 ≤ F x) (h1 : ∀ x, F x ≤ 1) :
    0 ≤ ∫ x, F x ∂S.m ∧ ∫ x, F x ∂S.m ≤ 1 := by
  constructor
  · exact integral_nonneg h0
  · have := integral_mono_of_nonneg (μ := S.m) (Filter.Eventually.of_forall h0)
      (integrable_const (1 : ℝ)) (Filter.Eventually.of_forall h1)
    simpa using this

/-- **Lemma `lem:wm-extension`, Part (W).**  If `D` is CSZ and `E` is a weakly mixing extension of
`D`, then `E` is CSZ. -/
theorem CSZ_of_weaklyMixingExtension {S : MPS.{0}} [StandardBorelSpace S.X] (D E : Factor S)
    (hDE : D.σ ≤ E.σ) (hD : D.CSZ) (hE : WeaklyMixingExtension D E) : E.CSZ := by
  unfold Factor.CSZ at hD ⊢
  intro C A hA hpos t ht i
  have hAm : MeasurableSet A := E.le _ hA
  set ind : S.X → ℝ := A.indicator (1 : S.X → ℝ) with hind
  set g : S.X → ℝ := clipCond D ind with hg
  have hind_meas : Measurable ind := measurable_const.indicator hAm
  have hind_measE : Measurable[E.σ] ind := measurable_const.indicator hA
  have hind_nn : ∀ x, 0 ≤ ind x := fun x => by
    by_cases hx : x ∈ A
    · simp [hind, Set.indicator_of_mem hx]
    · simp [hind, Set.indicator_of_notMem hx]
  have hind_le : ∀ x, |ind x| ≤ 1 := fun x => by
    by_cases hx : x ∈ A
    · simp [hind, Set.indicator_of_mem hx]
    · simp [hind, Set.indicator_of_notMem hx]
  have hind_le1 : ∀ x, ind x ≤ 1 := fun x => (le_abs_self _).trans (hind_le x)
  have hg_mem := clipCond_mem D ind
  -- the clipped expectation has positive integral
  have hgint : 0 < ∫ x, g x ∂S.m := by
    have h1 : ∫ x, g x ∂S.m = ∫ x, S.m[ind | D.σ] x ∂S.m :=
      integral_congr_ae (clipCond_ae D hind_meas hind_nn hind_le)
    have h2 : ∫ x, S.m[ind | D.σ] x ∂S.m = ∫ x, ind x ∂S.m := integral_condExp D.le
    have h3 : ∫ x, ind x ∂S.m = S.m.real A := integral_indicator_one hAm
    have h4 : 0 < S.m.real A := by
      unfold Measure.real
      exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
    rw [h1, h2, h3]
    exact h4
  -- positivity of the functional sequence
  have hb_pos := (csz_functions_iff D C ht i).1 (fun A' hA' hp' => hD C A' hA' hp' t ht i) g
    (clipCond_meas D ind) (fun x => (hg_mem x).1) ⟨1, fun x => (hg_mem x).2⟩ hgint
  -- the two sequences
  set a : ℕ → ℝ := fun n => ∫ x, ∏ s ∈ range (t + 1), ind (S.T^[s * (C.base ^ i * C.enum n)] x)
    ∂S.m with ha
  set b : ℕ → ℝ := fun n => ∫ x, ∏ s ∈ range (t + 1), g (S.T^[s * (C.base ^ i * C.enum n)] x)
    ∂S.m with hb
  have ha_eq : (fun n => S.multiCorr A t (C.base ^ i * C.enum n)) = a := by
    funext n
    rw [ha, multiCorr_eq_integral S hAm t _]
  rw [ha_eq]
  have ha01 : ∀ n, 0 ≤ a n ∧ a n ≤ 1 := fun n =>
    integral_mem_unit _ (fun x => (prod_mem_unit ind hind_nn hind_le1 t _ x).1)
      (fun x => (prod_mem_unit ind hind_nn hind_le1 t _ x).2)
  have hb01 : ∀ n, 0 ≤ b n ∧ b n ≤ 1 := fun n =>
    integral_mem_unit _ (fun x => (prod_mem_unit g (fun y => (hg_mem y).1)
      (fun y => (hg_mem y).2) t _ x).1)
      (fun x => (prod_mem_unit g (fun y => (hg_mem y).1) (fun y => (hg_mem y).2) t _ x).2)
  -- the shifts `s_j = (j+1) b^i`, with `s_j k_n = (j+1) (b^i k_n)`
  set s : ℕ → ℕ := fun j => (j + 1) * C.base ^ i with hs_def
  have hBpos : 0 < C.base ^ i := pow_pos (by have := C.three_le_base; omega) i
  have hs : GoodExp s t := by
    refine ⟨fun j _ => ?_, fun j j' hjj' hj' => ?_⟩
    · exact Nat.mul_pos (Nat.succ_pos j) hBpos
    · show (j + 1) * C.base ^ i < (j' + 1) * C.base ^ i
      exact Nat.mul_lt_mul_of_pos_right (by omega) hBpos
  -- the products over `range t` on each block
  have hPmeas : ∀ n, Measurable (fun x => ∏ j ∈ range t, ind (S.T^[s j * C.enum n] x)) :=
    fun n => Finset.measurable_prod _ fun j _ => hind_meas.comp (S.measurable_T.iterate _)
  have hQmeas : ∀ n, Measurable[D.σ] (fun x => ∏ j ∈ range t, g (S.T^[s j * C.enum n] x)) :=
    fun n => Finset.measurable_prod _ fun j _ => measurable_comp_iter D (clipCond_meas D ind) _
  have hPQbd : ∀ n x, |∏ j ∈ range t, ind (S.T^[s j * C.enum n] x)| ≤ 1 ∧
      |∏ j ∈ range t, g (S.T^[s j * C.enum n] x)| ≤ 1 := by
    intro n x
    constructor
    · rw [abs_of_nonneg (Finset.prod_nonneg fun j _ => hind_nn _)]
      exact Finset.prod_le_one₀ (fun j _ => hind_nn _) fun j _ => hind_le1 _
    · rw [abs_of_nonneg (Finset.prod_nonneg fun j _ => (hg_mem _).1)]
      exact Finset.prod_le_one₀ (fun j _ => (hg_mem _).1) fun j _ => (hg_mem _).2
  -- the sequences as integrals of `ind · P_n` and `g · Q_n`
  have hA : ∀ n, a n = ∫ x, ind x * ∏ j ∈ range t, ind (S.T^[s j * C.enum n] x) ∂S.m := by
    intro n
    simp only [ha]
    rw [integral_prod_range_succ' ind t (C.base ^ i * C.enum n)]
    congr 1
    funext x
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 2
    simp only [hs_def]
    ring
  have hB : ∀ n, b n = ∫ x, g x * ∏ j ∈ range t, g (S.T^[s j * C.enum n] x) ∂S.m := by
    intro n
    simp only [hb]
    rw [integral_prod_range_succ' g t (C.base ^ i * C.enum n)]
    congr 1
    funext x
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 2
    simp only [hs_def]
    ring
  -- pairing the indicator with the `D`-measurable products
  have hpair : ∀ n, ∫ x, ind x * ∏ j ∈ range t, g (S.T^[s j * C.enum n] x) ∂S.m = b n := by
    intro n
    rw [hB n]
    exact integral_ind_mul_eq_clip D hAm (hQmeas n) (K := 1) (fun x => (hPQbd n x).2)
  -- the window averages of the differences
  set V : ℕ × ℕ → S.X → ℝ := fun p x => (((p.2 - p.1 : ℕ) : ℝ))⁻¹ * ∑ n ∈ Ico p.1 p.2,
      (∏ j ∈ range t, ind (S.T^[s j * C.enum n] x) - ∏ j ∈ range t, g (S.T^[s j * C.enum n] x))
    with hV
  have hVmeas : ∀ p, Measurable (V p) := fun p =>
    measurable_const.mul (Finset.measurable_sum _ fun n _ => (hPmeas n).sub
      ((hQmeas n).mono D.le le_rfl))
  have hVb : ∀ p x, |V p x| ≤ 2 := by
    intro p x
    simp only [hV]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
    rcases Nat.eq_zero_or_pos (p.2 - p.1) with h0 | hpos
    · simp [h0]
    have hLpos : (0 : ℝ) < ((p.2 - p.1 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hsum : |∑ n ∈ Ico p.1 p.2, (∏ j ∈ range t, ind (S.T^[s j * C.enum n] x)
        - ∏ j ∈ range t, g (S.T^[s j * C.enum n] x))| ≤ 2 * ((p.2 - p.1 : ℕ) : ℝ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ n ∈ Ico p.1 p.2, |∏ j ∈ range t, ind (S.T^[s j * C.enum n] x)
            - ∏ j ∈ range t, g (S.T^[s j * C.enum n] x)|
          ≤ ∑ n ∈ Ico p.1 p.2, (2 : ℝ) := by
            refine Finset.sum_le_sum fun n _ => ?_
            have h1 := hPQbd n x
            have h2 := abs_sub (∏ j ∈ range t, ind (S.T^[s j * C.enum n] x))
              (∏ j ∈ range t, g (S.T^[s j * C.enum n] x))
            linarith
        _ = 2 * ((p.2 - p.1 : ℕ) : ℝ) := by simp; ring
    calc ((p.2 - p.1 : ℕ) : ℝ)⁻¹ * |∑ n ∈ Ico p.1 p.2, (∏ j ∈ range t, ind (S.T^[s j * C.enum n] x)
          - ∏ j ∈ range t, g (S.T^[s j * C.enum n] x))|
        ≤ ((p.2 - p.1 : ℕ) : ℝ)⁻¹ * (2 * ((p.2 - p.1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hLpos.le)
      _ = 2 := by
        have hne := hLpos.ne'
        field_simp
  have hIP : ∀ n, Integrable (fun x => ind x * ∏ j ∈ range t, ind (S.T^[s j * C.enum n] x)) S.m :=
    fun n => integrable_of_bdd_const (hind_meas.mul (hPmeas n)) (K := 1) fun x => by
      rw [abs_mul]
      exact mul_le_one₀ (hind_le x) (abs_nonneg _) (hPQbd n x).1
  have hIQ : ∀ n, Integrable (fun x => ind x * ∏ j ∈ range t, g (S.T^[s j * C.enum n] x)) S.m :=
    fun n => integrable_of_bdd_const (hind_meas.mul ((hQmeas n).mono D.le le_rfl)) (K := 1)
      fun x => by
        rw [abs_mul]
        exact mul_le_one₀ (hind_le x) (abs_nonneg _) (hPQbd n x).2
  have hint : ∀ n, Integrable (fun x => ind x * (∏ j ∈ range t, ind (S.T^[s j * C.enum n] x)
      - ∏ j ∈ range t, g (S.T^[s j * C.enum n] x))) S.m := fun n => by
    have e : (fun x => ind x * (∏ j ∈ range t, ind (S.T^[s j * C.enum n] x)
        - ∏ j ∈ range t, g (S.T^[s j * C.enum n] x)))
        = fun x => ind x * ∏ j ∈ range t, ind (S.T^[s j * C.enum n] x)
          - ind x * ∏ j ∈ range t, g (S.T^[s j * C.enum n] x) := by
      funext x
      ring
    rw [e]
    exact (hIP n).sub (hIQ n)
  have hterm : ∀ n, ∫ x, ind x * (∏ j ∈ range t, ind (S.T^[s j * C.enum n] x)
      - ∏ j ∈ range t, g (S.T^[s j * C.enum n] x)) ∂S.m = a n - b n := by
    intro n
    have e : ∀ x, ind x * (∏ j ∈ range t, ind (S.T^[s j * C.enum n] x)
        - ∏ j ∈ range t, g (S.T^[s j * C.enum n] x))
        = ind x * ∏ j ∈ range t, ind (S.T^[s j * C.enum n] x)
          - ind x * ∏ j ∈ range t, g (S.T^[s j * C.enum n] x) := fun x => by ring
    simp only [e]
    rw [integral_sub (hIP n) (hIQ n), ← hA n, hpair n]
  -- the difference of the uniform averages, as the pairing with `V`
  have hdiff : ∀ p : ℕ × ℕ, uniformAvg a p.1 p.2 - uniformAvg b p.1 p.2
      = ∫ x, ind x * V p x ∂S.m := by
    intro p
    have e2 : ∀ x, ind x * V p x = ((p.2 - p.1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Ico p.1 p.2,
        ind x * (∏ j ∈ range t, ind (S.T^[s j * C.enum n] x)
          - ∏ j ∈ range t, g (S.T^[s j * C.enum n] x)) := fun x => by
      simp only [hV]
      rw [mul_left_comm, Finset.mul_sum]
    have hI : ∫ x, ind x * V p x ∂S.m = ((p.2 - p.1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Ico p.1 p.2, (a n - b n) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall e2), integral_const_mul,
        integral_finsetSum _ (fun n _ => hint n)]
      congr 1
      exact Finset.sum_congr rfl fun n _ => hterm n
    rw [hI]
    simp only [uniformAvg]
    rw [div_eq_inv_mul, div_eq_inv_mul, ← mul_sub, Finset.sum_sub_distrib]
  -- the bound of the difference by the `L²` norm of `V`
  have hfinV : ∀ p, eLpNorm (V p) 2 S.m ≠ ⊤ := fun p =>
    (MemLp.of_bound (hVmeas p).aestronglyMeasurable 2 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hVb p x)).eLpNorm_ne_top
  have hbound : ∀ p, |uniformAvg a p.1 p.2 - uniformAvg b p.1 p.2|
      ≤ (eLpNorm (V p) 2 S.m).toReal := by
    intro p
    rw [hdiff p]
    have hVint : Integrable (fun x => |V p x|) S.m :=
      integrable_of_bdd_const (hVmeas p).abs (K := 2) fun x => by
        rw [abs_abs]
        exact hVb p x
    calc |∫ x, ind x * V p x ∂S.m| ≤ ∫ x, |ind x * V p x| ∂S.m := abs_integral_le_integral_abs
      _ ≤ ∫ x, |V p x| ∂S.m := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
          hVint (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (hind_le x)
      _ ≤ (eLpNorm (V p) 2 S.m).toReal :=
        integral_abs_le_eLpNorm_two (hVmeas p).aestronglyMeasurable (hfinV p)
  -- the averages of the differences tend to zero, by the main estimate
  have hfE' : ∀ j, j < t → Measurable[E.σ] ((fun _ : ℕ => ind) j) := fun j _ => hind_measE
  have hfb' : ∀ j, j < t → ∀ x, |(fun _ : ℕ => ind) j x| ≤ 1 := fun j _ x => hind_le x
  have hwm := wm_extension_tendsto C t D E hDE (wmHyp_of_wmExt hE) s hs (fun _ => ind)
    zero_le_one hfE' hfb'
  have htV : Tendsto (fun p : ℕ × ℕ => eLpNorm (V p) 2 S.m) uniformFilter (𝓝 0) := by
    refine hwm.congr' (Filter.Eventually.of_forall fun p => ?_)
    apply eLpNorm_congr_ae
    filter_upwards [(Filter.eventually_all_finset (Ico p.1 p.2)).2 fun n _ =>
      (Filter.eventually_all_finset (range t)).2 fun j _ =>
        (S.measurePreserving_T_iterate (s j * C.enum n)).quasiMeasurePreserving.ae
          (clipCond_ae D hind_meas hind_nn hind_le)] with x hx
    simp only [hV]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    exact (hx n hn j hj).symm
  have hT : Tendsto (fun p : ℕ × ℕ => (eLpNorm (V p) 2 S.m).toReal) uniformFilter (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal_iff hfinV ENNReal.zero_ne_top).2 htV
    simpa using h
  have hd : Tendsto (fun p : ℕ × ℕ => uniformAvg a p.1 p.2 - uniformAvg b p.1 p.2) uniformFilter
      (𝓝 0) :=
    squeeze_zero_norm' (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact hbound p) hT
  exact uniformLiminf_pos_of_sub_tendsto a b ha01 hb01 hd hb_pos

end MPS

end CantorSzemeredi

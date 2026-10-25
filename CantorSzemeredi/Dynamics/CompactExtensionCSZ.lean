/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.CompactCSZ
import CantorSzemeredi.Dynamics.Localize

/-!
# Compact extensions are CSZ

Blueprint: `blueprint/src/chapter/compact.tex`, `thm:compact-extension`.

A compact extension `E | D` of a CSZ factor `D` is CSZ (in the set form of Definition
`def:csz`).  The proof reduces the set form to the function form of `CompactCSZ.lean` by
passing to the power system `T^{b^{i}}` (Remark `rem:compact-dilation`), localizing the
indicator with `exists_condCompact_restrict`, and comparing integrals.
-/

namespace CantorSzemeredi

open MeasureTheory Filter

namespace MPS

variable {S : MPS}

/-- Multiple correlations along the power system are those of `S` at the product step. -/
theorem multiCorr_pow (S : MPS) (k : ℕ) (A : Set S.X) (t d : ℕ) :
    (S.pow k).multiCorr A t d = S.multiCorr A t (k * d) := by
  have hit : ∀ s, (S.pow k).T^[s * d] = S.T^[s * (k * d)] := fun s => by
    change (S.T^[k])^[s * d] = S.T^[s * (k * d)]
    rw [← Function.iterate_mul]
    congr 1
    ring
  unfold MPS.multiCorr
  simp only [hit]
  rfl

/-- The multiple correlation as an integral of a product of indicators. -/
theorem multiCorr_eq_integral (S : MPS) {A : Set S.X} (hA : MeasurableSet A) (t d : ℕ) :
    S.multiCorr A t d
      = ∫ x, ∏ s ∈ Finset.range (t + 1), A.indicator (1 : S.X → ℝ) (S.T^[s * d] x) ∂S.m := by
  have hpt : (fun x => ∏ s ∈ Finset.range (t + 1), A.indicator (1 : S.X → ℝ) (S.T^[s * d] x))
      = (⋂ s ∈ Finset.range (t + 1), (S.T^[s * d]) ⁻¹' A).indicator (1 : S.X → ℝ) := by
    funext x
    by_cases hx : x ∈ ⋂ s ∈ Finset.range (t + 1), (S.T^[s * d]) ⁻¹' A
    · rw [Set.indicator_of_mem hx]
      apply Finset.prod_eq_one
      intro s hs
      have hxs : x ∈ (S.T^[s * d]) ⁻¹' A := Set.mem_iInter₂.1 hx s hs
      rw [Set.indicator_of_mem (show S.T^[s * d] x ∈ A from hxs)]
      rfl
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨s, hs, hxs⟩ : ∃ s ∈ Finset.range (t + 1), x ∉ (S.T^[s * d]) ⁻¹' A := by
        by_contra hcon
        push Not at hcon
        exact hx (Set.mem_iInter₂.2 fun s hs => hcon s hs)
      apply Finset.prod_eq_zero hs
      rw [Set.indicator_of_notMem (show S.T^[s * d] x ∉ A from hxs)]
  have hmeas : MeasurableSet (⋂ s ∈ Finset.range (t + 1), (S.T^[s * d]) ⁻¹' A) :=
    Finset.measurableSet_biInter _ fun s _ =>
      measurableSet_preimage (S.measurable_T.iterate _) hA
  rw [hpt, integral_indicator_one hmeas]
  rfl

/-- The uniform `liminf` is monotone for sequences in `[0,1]`. -/
theorem uniformLiminf_mono {a b : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (hb1 : ∀ n, b n ≤ 1) (hab : ∀ n, a n ≤ b n) :
    uniformLiminf a ≤ uniformLiminf b := by
  have hA : ∀ M N, uniformAvg a M N ≤ uniformAvg b M N := by
    intro M N
    unfold uniformAvg
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun n _ => hab n) (by positivity)
  change Filter.liminf (fun p : ℕ × ℕ => uniformAvg a p.1 p.2) uniformFilter
      ≤ Filter.liminf (fun p : ℕ × ℕ => uniformAvg b p.1 p.2) uniformFilter
  have hbdd_a : Filter.IsBoundedUnder (· ≥ ·) uniformFilter
      (fun p : ℕ × ℕ => uniformAvg a p.1 p.2) :=
    Filter.isBoundedUnder_of ⟨0, fun p => uniformAvg_nonneg ha0 p.1 p.2⟩
  have hbdd_b : Filter.IsBoundedUnder (· ≤ ·) uniformFilter
      (fun p : ℕ × ℕ => uniformAvg b p.1 p.2) :=
    Filter.isBoundedUnder_of ⟨1, fun p => uniformAvg_le_one' hb1 p.1 p.2⟩
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun p => hA p.1 p.2) hbdd_a
    hbdd_b.isCoboundedUnder_ge

/-- **Theorem `thm:compact-extension`.**  A compact extension `E | D` of a CSZ factor `D` is
CSZ. -/
theorem csz_sets_of_compactExtension (D E : Factor S) (hD : D.CSZ) (hE : CompactExtension D E) :
    E.CSZ := by
  unfold Factor.CSZ
  intro C A hA hpos t ht i
  -- the CSZ hypothesis for the power system `T^{b^i}`, at dilation `j`
  have hD' : ∀ A' : Set S.X, MeasurableSet[(D.toPow (C.base ^ i)).σ] A' →
      0 < (S.pow (C.base ^ i)).m A' → ∀ j : ℕ,
      0 < uniformLiminf (fun n => (S.pow (C.base ^ i)).multiCorr A' t (C.base ^ j * C.enum n)) := by
    intro A' hA' hpos' j
    have h := hD C A' hA' hpos' t ht (i + j)
    have heq : (fun n => (S.pow (C.base ^ i)).multiCorr A' t (C.base ^ j * C.enum n))
        = fun n => S.multiCorr A' t (C.base ^ (i + j) * C.enum n) := by
      funext n
      rw [multiCorr_pow, pow_add, mul_assoc]
    rw [heq]
    exact h
  -- localize the indicator of `A`
  have hAamb : MeasurableSet A := E.le A hA
  have hg0m : Measurable (A.indicator (1 : S.X → ℝ)) := measurable_const.indicator hAamb
  have hfE : AEStronglyMeasurable[(E.toPow (C.base ^ i)).σ] (A.indicator (1 : S.X → ℝ)) S.m :=
    (stronglyMeasurable_const.indicator hA).aestronglyMeasurable
  have hbd : ∀ᵐ x ∂S.m, ‖A.indicator (1 : S.X → ℝ) x‖ ≤ 1 :=
    ae_of_all _ fun x => by
      by_cases hx : x ∈ A <;> simp [hx]
  have hMemLp : MemLp (A.indicator (1 : S.X → ℝ)) 2 S.m :=
    MemLp.of_bound hg0m.aestronglyMeasurable 1 hbd
  have hμA : S.m A ≠ ⊤ := measure_ne_top _ _
  have hμpos : 0 < (S.m A).toReal := ENNReal.toReal_pos hpos.ne' hμA
  set η : ℝ := (S.m A).toReal / 2 with hη_def
  have hηpos : 0 < η := by rw [hη_def]; positivity
  obtain ⟨Astar₀, hAsD, hAsm, hcc⟩ :=
    exists_condCompact_restrict (D := D.toPow (C.base ^ i)) (E := E.toPow (C.base ^ i))
      (hE.pow (C.base ^ i)) hfE hMemLp hηpos
  set Astar : Set S.X := Astar₀ with hAs_def
  -- the localized indicator is the indicator of `Astar ∩ A`
  set h : S.X → ℝ := Astar.indicator (A.indicator (1 : S.X → ℝ)) with hh_def
  have heq : h = (Astar ∩ A).indicator (1 : S.X → ℝ) := by
    rw [hh_def, Set.indicator_indicator]
  have hh0 : ∀ x, 0 ≤ h x := fun x => by
    rw [heq]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hh1 : ∀ x, h x ≤ 1 := fun x => by
    rw [heq]
    by_cases hx : x ∈ Astar ∩ A
    · rw [Set.indicator_of_mem hx]
      exact le_rfl
    · rw [Set.indicator_of_notMem hx]
      exact zero_le_one
  have hhle : ∀ x, h x ≤ A.indicator (1 : S.X → ℝ) x := fun x => by
    rw [heq]
    by_cases hx : x ∈ Astar ∩ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx.2]
    · rw [Set.indicator_of_notMem hx]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hhm : Measurable h := by
    rw [heq]
    exact measurable_const.indicator ((D.le _ hAsD).inter hAamb)
  have hbdh : ∀ᵐ x ∂S.m, ‖h x‖ ≤ 1 := ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hh0 x)]
    exact hh1 x
  have hhMem : MemLp h 2 S.m := MemLp.of_bound hhm.aestronglyMeasurable 1 hbdh
  -- the set `A ∩ Astar` has positive measure
  have hAAs : 0 < S.m (Astar ∩ A) := by
    by_contra hcon
    have hz : S.m (Astar ∩ A) = 0 := le_antisymm (not_lt.1 hcon) (by positivity)
    have hsub : A ⊆ (Astar ∩ A) ∪ Astarᶜ := fun x hx => by
      by_cases hs : x ∈ Astar
      · exact Or.inl ⟨hs, hx⟩
      · exact Or.inr hs
    have hle : S.m A ≤ S.m (Astar ∩ A) + S.m Astarᶜ :=
      (measure_mono hsub).trans (measure_union_le _ _)
    have hlt : ENNReal.ofReal η < S.m A :=
      (ENNReal.ofReal_lt_iff_lt_toReal hηpos.le hμA).2 (by rw [hη_def]; linarith)
    rw [hz, zero_add] at hle
    exact lt_irrefl _ (lt_of_le_of_lt (hle.trans hAsm) hlt)
  have hint_pos : 0 < ∫ x, h x ∂S.m := by
    rw [heq, integral_indicator_one ((D.le _ hAsD).inter hAamb), measureReal_def]
    exact ENNReal.toReal_pos hAAs.ne' (measure_ne_top _ _)
  -- the core theorem on the power system `T^{b^i}`
  have hcore := compact_core C (D.toPow (C.base ^ i)) (E.toPow (C.base ^ i)) (t := t) hD' hhm
    hh0 hh1 hhMem ht hint_pos hcc
  -- comparison with the indicator of `A`
  have hg0_0 : ∀ x, 0 ≤ A.indicator (1 : S.X → ℝ) x := fun x =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hg0_1 : ∀ x, A.indicator (1 : S.X → ℝ) x ≤ 1 := fun x => by
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      exact le_of_eq (Pi.one_apply x)
    · rw [Set.indicator_of_notMem hx]
      exact zero_le_one
  have hint_le : ∀ n, ∫ x, ∏ s ∈ Finset.range (t + 1), h ((S.pow (C.base ^ i)).T^[s * C.enum n] x)
      ∂(S.pow (C.base ^ i)).m
      ≤ ∫ x, ∏ s ∈ Finset.range (t + 1),
          A.indicator (1 : S.X → ℝ) ((S.pow (C.base ^ i)).T^[s * C.enum n] x)
        ∂(S.pow (C.base ^ i)).m := fun n => by
    have hPh : Integrable (fun x => ∏ s ∈ Finset.range (t + 1),
        h ((S.pow (C.base ^ i)).T^[s * C.enum n] x)) (S.pow (C.base ^ i)).m :=
      integrable_of_unit_bound (Finset.measurable_prod _ fun s _ =>
          hhm.comp ((S.pow (C.base ^ i)).measurable_T.iterate _))
        (fun x => Finset.prod_nonneg fun s _ => hh0 _)
        (fun x => Finset.prod_le_one₀ (fun s _ => hh0 _) fun s _ => hh1 _)
    have hPg : Integrable (fun x => ∏ s ∈ Finset.range (t + 1),
        A.indicator (1 : S.X → ℝ) ((S.pow (C.base ^ i)).T^[s * C.enum n] x))
        (S.pow (C.base ^ i)).m :=
      integrable_of_unit_bound (Finset.measurable_prod _ fun s _ =>
          hg0m.comp ((S.pow (C.base ^ i)).measurable_T.iterate _))
        (fun x => Finset.prod_nonneg fun s _ => hg0_0 _)
        (fun x => Finset.prod_le_one₀ (fun s _ => hg0_0 _) fun s _ => hg0_1 _)
    exact integral_mono hPh hPg fun x =>
      Finset.prod_le_prod₀ (fun s _ => hh0 _) (fun s _ => hhle _)
  have hid : ∀ n, ∫ x, ∏ s ∈ Finset.range (t + 1),
        A.indicator (1 : S.X → ℝ) ((S.pow (C.base ^ i)).T^[s * C.enum n] x)
        ∂(S.pow (C.base ^ i)).m
      = S.multiCorr A t (C.base ^ i * C.enum n) := fun n =>
    (multiCorr_eq_integral (S.pow (C.base ^ i)) hAamb t (C.enum n)).symm.trans
      (multiCorr_pow S (C.base ^ i) A t (C.enum n))
  have hmono := uniformLiminf_mono (a := fun n => ∫ x, ∏ s ∈ Finset.range (t + 1),
        h ((S.pow (C.base ^ i)).T^[s * C.enum n] x) ∂(S.pow (C.base ^ i)).m)
      (b := fun n => ∫ x, ∏ s ∈ Finset.range (t + 1),
        A.indicator (1 : S.X → ℝ) ((S.pow (C.base ^ i)).T^[s * C.enum n] x)
        ∂(S.pow (C.base ^ i)).m)
      (fun n => integral_nonneg fun x => Finset.prod_nonneg fun s _ => hh0 _)
      (fun n => integral_nonneg fun x => Finset.prod_nonneg fun s _ => hg0_0 _)
      (fun n => integral_prod_le_one (S := S.pow (C.base ^ i)) hg0m hg0_0 hg0_1 t (C.enum n))
      hint_le
  have hlim : uniformLiminf (fun n => ∫ x, ∏ s ∈ Finset.range (t + 1),
        A.indicator (1 : S.X → ℝ) ((S.pow (C.base ^ i)).T^[s * C.enum n] x)
        ∂(S.pow (C.base ^ i)).m)
      = uniformLiminf (fun n => S.multiCorr A t (C.base ^ i * C.enum n)) :=
    congrArg uniformLiminf (funext hid)
  exact lt_of_lt_of_le hcore (hmono.trans_eq hlim)

/-- Scaling by a positive constant keeps a positive uniform `liminf` positive. -/
theorem uniformLiminf_const_mul_pos {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    {K : ℝ} (hK : 0 < K) (hpos : 0 < uniformLiminf a) :
    0 < uniformLiminf (fun n => K * a n) := by
  have hbdd : Filter.IsBoundedUnder (· ≥ ·) uniformFilter
      (fun p : ℕ × ℕ => uniformAvg a p.1 p.2) :=
    Filter.isBoundedUnder_of ⟨0, fun p => uniformAvg_nonneg ha0 p.1 p.2⟩
  have hliminf : uniformLiminf a = Filter.liminf (fun p : ℕ × ℕ => uniformAvg a p.1 p.2)
      uniformFilter := rfl
  have hev : {p : ℕ × ℕ | uniformLiminf a / 2 < uniformAvg a p.1 p.2} ∈ uniformFilter := by
    apply Filter.eventually_lt_of_lt_liminf
    · rw [← hliminf]
      linarith
    · exact hbdd
  obtain ⟨L, hL⟩ := mem_uniformFilter_iff.1 hev
  have hscale : ∀ M N, uniformAvg (fun n => K * a n) M N = K * uniformAvg a M N := by
    intro M N
    unfold uniformAvg
    rw [← Finset.mul_sum]
    ring
  have hbdd_top : Filter.IsBoundedUnder (· ≤ ·) uniformFilter
      (fun p : ℕ × ℕ => uniformAvg (fun n => K * a n) p.1 p.2) :=
    Filter.isBoundedUnder_of ⟨K, fun p => by
      rw [hscale]
      have := uniformAvg_le_one' ha1 p.1 p.2
      nlinarith⟩
  change 0 < Filter.liminf (fun p : ℕ × ℕ => uniformAvg (fun n => K * a n) p.1 p.2) uniformFilter
  refine lt_of_lt_of_le (?_ : 0 < K * (uniformLiminf a / 2))
    (Filter.le_liminf_of_le hbdd_top.isCoboundedUnder_ge ?_)
  · exact mul_pos hK (half_pos hpos)
  · refine mem_uniformFilter_iff.2 ⟨L, fun M N hW => ?_⟩
    show K * (uniformLiminf a / 2) ≤ uniformAvg (fun n => K * a n) M N
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (le_of_lt (hL M N hW)) hK.le

/-- **Lemma `lem:csz-functions`** (one direction, in the form needed).  If `E` is CSZ, then for an
`E`-measurable `0 ≤ f ≤ 1` with positive integral, the uniform `liminf` of the averages of
`∏_{s ≤ t} T^{s b^i k_n} f` is positive. -/
theorem csz_functions_of_csz (E : Factor S) {t : ℕ} (C : CantorData) (i : ℕ)
    (hEcsz : ∀ A : Set S.X, MeasurableSet[E.σ] A → 0 < S.m A →
      0 < uniformLiminf (fun n => S.multiCorr A t (C.base ^ i * C.enum n)))
    {f : S.X → ℝ} (hfm : Measurable[E.σ] f) (h0 : ∀ x, 0 ≤ f x)
    (h1 : ∀ x, f x ≤ 1) (hpos : 0 < ∫ x, f x ∂S.m) :
    0 < uniformLiminf (fun n => ∫ x, ∏ s ∈ Finset.range (t + 1),
      f (S.T^[s * (C.base ^ i * C.enum n)] x) ∂S.m) := by
  have hfmA : Measurable f := hfm.mono E.le le_rfl
  -- a level set of positive measure
  obtain ⟨c, hc, hAc⟩ : ∃ c : ℝ, 0 < c ∧ 0 < S.m {x | c < f x} := by
    by_contra hcon
    push Not at hcon
    have hsub : {x | ¬ f x = 0} ⊆ ⋃ k : ℕ, {x | 1 / ((k : ℝ) + 1) < f x} := by
      intro x hx
      have hfx : 0 < f x := lt_of_le_of_ne (h0 x) (Ne.symm hx)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hfx
      exact Set.mem_iUnion.2 ⟨k, hk⟩
    have hnull : S.m {x | ¬ f x = 0} = 0 := by
      refine le_antisymm ((measure_mono hsub).trans
        (le_of_eq (measure_iUnion_null fun k => ?_))) (by positivity)
      exact le_antisymm (hcon _ (by positivity)) (by positivity)
    have hae : f =ᵐ[S.m] 0 := ae_iff.2 hnull
    have : ∫ x, f x ∂S.m = 0 := integral_eq_zero_of_ae hae
    linarith
  set A : Set S.X := {x | c < f x} with hA_def
  have hAE : MeasurableSet[E.σ] A := hfm measurableSet_Ioi
  have hAm : MeasurableSet A := E.le A hAE
  -- the set form gives positivity for the indicator of `A`
  have hcsz := hEcsz A hAE hAc
  have hb_eq : ∀ n, S.multiCorr A t (C.base ^ i * C.enum n)
      = ∫ x, ∏ s ∈ Finset.range (t + 1), A.indicator (1 : S.X → ℝ)
          (S.T^[s * (C.base ^ i * C.enum n)] x) ∂S.m :=
    fun n => multiCorr_eq_integral S hAm t _
  have hb0 : ∀ n, 0 ≤ ∫ x, ∏ s ∈ Finset.range (t + 1), A.indicator (1 : S.X → ℝ)
      (S.T^[s * (C.base ^ i * C.enum n)] x) ∂S.m := fun n =>
    integral_nonneg fun x => Finset.prod_nonneg fun s _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hb1 : ∀ n, ∫ x, ∏ s ∈ Finset.range (t + 1), A.indicator (1 : S.X → ℝ)
      (S.T^[s * (C.base ^ i * C.enum n)] x) ∂S.m ≤ 1 := fun n => by
    have h0' : ∀ x, 0 ≤ A.indicator (1 : S.X → ℝ) x := fun x =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have h1' : ∀ x, A.indicator (1 : S.X → ℝ) x ≤ 1 := fun x => by
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        exact le_of_eq (Pi.one_apply x)
      · rw [Set.indicator_of_notMem hx]
        exact zero_le_one
    exact integral_prod_le_one (S := S) (measurable_const.indicator hAm) h0' h1' t
      (C.base ^ i * C.enum n)
  -- the comparison `c · 1_A ≤ f`
  have hfge : ∀ x, c * A.indicator (1 : S.X → ℝ) x ≤ f x := fun x => by
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      exact le_of_lt hx
    · rw [Set.indicator_of_notMem hx, mul_zero]
      exact h0 x
  have hprod : ∀ n, c ^ (t + 1) * (∫ x, ∏ s ∈ Finset.range (t + 1), A.indicator (1 : S.X → ℝ)
      (S.T^[s * (C.base ^ i * C.enum n)] x) ∂S.m)
      ≤ ∫ x, ∏ s ∈ Finset.range (t + 1), f (S.T^[s * (C.base ^ i * C.enum n)] x) ∂S.m := by
    intro n
    rw [← integral_const_mul]
    have hPg : Integrable (fun x => ∏ s ∈ Finset.range (t + 1), A.indicator (1 : S.X → ℝ)
        (S.T^[s * (C.base ^ i * C.enum n)] x)) S.m :=
      integrable_of_unit_bound (Finset.measurable_prod _ fun s _ =>
          (measurable_const.indicator hAm).comp (S.measurable_T.iterate _))
        (fun x => Finset.prod_nonneg fun s _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        (fun x => Finset.prod_le_one₀ (fun s _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
          fun s _ => by
            by_cases hx : S.T^[s * (C.base ^ i * C.enum n)] x ∈ A
            · rw [Set.indicator_of_mem hx]
              exact le_of_eq (Pi.one_apply _)
            · rw [Set.indicator_of_notMem hx]
              exact zero_le_one)
    have hPf : Integrable (fun x => ∏ s ∈ Finset.range (t + 1),
        f (S.T^[s * (C.base ^ i * C.enum n)] x)) S.m :=
      integrable_of_unit_bound (Finset.measurable_prod _ fun s _ =>
          hfmA.comp (S.measurable_T.iterate _))
        (fun x => Finset.prod_nonneg fun s _ => h0 _)
        (fun x => Finset.prod_le_one₀ (fun s _ => h0 _) fun s _ => h1 _)
    have hpt : ∀ x, c ^ (t + 1) * ∏ s ∈ Finset.range (t + 1),
        A.indicator (1 : S.X → ℝ) (S.T^[s * (C.base ^ i * C.enum n)] x)
        ≤ ∏ s ∈ Finset.range (t + 1), f (S.T^[s * (C.base ^ i * C.enum n)] x) := fun x => by
      have hc' : c ^ (t + 1) = ∏ _s ∈ Finset.range (t + 1), c := by simp
      rw [hc', ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀
        (fun s _ => mul_nonneg hc.le (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
        (fun s _ => hfge _)
    exact integral_mono (hPg.const_mul _) hPf hpt
  have hcpos : 0 < c ^ (t + 1) := pow_pos hc _
  have hpos_b : 0 < uniformLiminf (fun n => ∫ x, ∏ s ∈ Finset.range (t + 1),
      A.indicator (1 : S.X → ℝ) (S.T^[s * (C.base ^ i * C.enum n)] x) ∂S.m) := by
    have heqf : (fun n => S.multiCorr A t (C.base ^ i * C.enum n)) = fun n =>
        ∫ x, ∏ s ∈ Finset.range (t + 1), A.indicator (1 : S.X → ℝ)
          (S.T^[s * (C.base ^ i * C.enum n)] x) ∂S.m := funext hb_eq
    rw [← heqf]
    exact hcsz
  have hscaled := uniformLiminf_const_mul_pos hb0 hb1 hcpos hpos_b
  have hfa0 : ∀ n, 0 ≤ ∫ x, ∏ s ∈ Finset.range (t + 1), f (S.T^[s * (C.base ^ i * C.enum n)] x)
      ∂S.m := fun n => integral_nonneg fun x => Finset.prod_nonneg fun s _ => h0 _
  have hfa1 : ∀ n, ∫ x, ∏ s ∈ Finset.range (t + 1), f (S.T^[s * (C.base ^ i * C.enum n)] x)
      ∂S.m ≤ 1 := fun n => integral_prod_le_one (S := S) hfmA h0 h1 t (C.base ^ i * C.enum n)
  exact lt_of_lt_of_le hscaled (uniformLiminf_mono
    (fun n => mul_nonneg hcpos.le (hb0 n)) hfa0 hfa1 hprod)

/-- **Theorem `thm:compact-extension`.**  A compact extension `E | D` of a CSZ factor `D` is CSZ:
for `t ≥ 1`, `i ≥ 0` and every `E`-measurable `0 ≤ f ≤ 1` with positive integral, the uniform
`liminf` of the averages of `∏_{s ≤ t} T^{s b^i k_n} f` is positive. -/
theorem CSZ_of_compactExtension (D E : Factor S) (hD : D.CSZ) (hE : CompactExtension D E)
    (C : CantorData) {t : ℕ} (ht : 1 ≤ t) (i : ℕ) {f : S.X → ℝ} (hfm : Measurable[E.σ] f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) (hpos : 0 < ∫ x, f x ∂S.m) :
    0 < uniformLiminf (fun n => ∫ x, ∏ s ∈ Finset.range (t + 1),
      f (S.T^[s * (C.base ^ i * C.enum n)] x) ∂S.m) :=
  csz_functions_of_csz E C i (fun A hA hp => csz_sets_of_compactExtension D E hD hE C A hA hp t ht i)
    hfm h0 h1 hpos

/-- **Lemma `lem:csz-functions`.**  For a factor `D`, a Cantor set `C`, `t ≥ 1` and `i`, the set
form of the CSZ property on `D` (for `A ∈ D` with `m(A) > 0`) is equivalent to the function form
(for bounded `D`-measurable `f ≥ 0` which is not a.e. zero). -/
theorem csz_functions_iff (D : Factor S) (C : CantorData) {t : ℕ} (ht : 1 ≤ t) (i : ℕ) :
    (∀ A : Set S.X, MeasurableSet[D.σ] A → 0 < S.m A →
      0 < uniformLiminf (fun n => S.multiCorr A t (C.base ^ i * C.enum n))) ↔
    (∀ f : S.X → ℝ, Measurable[D.σ] f → (∀ x, 0 ≤ f x) → (∃ K : ℝ, ∀ x, f x ≤ K) →
      0 < ∫ x, f x ∂S.m → 0 < uniformLiminf (fun n => ∫ x, ∏ s ∈ Finset.range (t + 1),
        f (S.T^[s * (C.base ^ i * C.enum n)] x) ∂S.m)) := by
  constructor
  · intro ha f hfm h0 hK hpos
    obtain ⟨K, hKf⟩ := hK
    set K' : ℝ := max K 1 with hK'_def
    have hK'pos : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
    set g : S.X → ℝ := fun x => f x / K' with hg_def
    have hgm : Measurable[D.σ] g := hfm.div_const K'
    have hgmA : Measurable g := hgm.mono D.le le_rfl
    have hg0 : ∀ x, 0 ≤ g x := fun x => div_nonneg (h0 x) hK'pos.le
    have hg1 : ∀ x, g x ≤ 1 := fun x => by
      rw [hg_def]
      simp only
      rw [div_le_one hK'pos]
      exact le_trans (hKf x) (le_max_left _ _)
    have hgpos : 0 < ∫ x, g x ∂S.m := by
      have : ∫ x, g x ∂S.m = (∫ x, f x ∂S.m) / K' := by
        rw [hg_def, integral_div]
      rw [this]
      exact div_pos hpos hK'pos
    have hcpos := csz_functions_of_csz D C i (t := t) (fun A hA hp => ha A hA hp) hgm hg0 hg1 hgpos
    have hfun : (fun n => ∫ x, ∏ s ∈ Finset.range (t + 1),
        f (S.T^[s * (C.base ^ i * C.enum n)] x) ∂S.m)
        = fun n => K' ^ (t + 1) * ∫ x, ∏ s ∈ Finset.range (t + 1),
          g (S.T^[s * (C.base ^ i * C.enum n)] x) ∂S.m := by
      funext n
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have hf : ∀ y, f y = K' * g y := fun y => by
        rw [hg_def]
        simp only
        field_simp
      simp only [hf, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [hfun]
    refine uniformLiminf_const_mul_pos (fun n => integral_nonneg fun x =>
      Finset.prod_nonneg fun s _ => hg0 _)
      (fun n => integral_prod_le_one (S := S) hgmA hg0 hg1 t (C.base ^ i * C.enum n))
      (pow_pos hK'pos _) hcpos
  · intro hb A hA hpos
    have hAamb : MeasurableSet A := D.le A hA
    have hind : 0 < ∫ x, A.indicator (1 : S.X → ℝ) x ∂S.m := by
      rw [integral_indicator_one hAamb, measureReal_def]
      exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
    have hmeas : Measurable[D.σ] (A.indicator (1 : S.X → ℝ)) :=
      measurable_const.indicator hA
    have h := hb (A.indicator (1 : S.X → ℝ)) hmeas
      (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
      ⟨1, fun x => by
        by_cases hx : x ∈ A
        · rw [Set.indicator_of_mem hx]
          exact le_of_eq (Pi.one_apply x)
        · rw [Set.indicator_of_notMem hx]
          exact zero_le_one⟩ hind
    have hfun : (fun n => ∫ x, ∏ s ∈ Finset.range (t + 1),
        A.indicator (1 : S.X → ℝ) (S.T^[s * (C.base ^ i * C.enum n)] x) ∂S.m)
        = fun n => S.multiCorr A t (C.base ^ i * C.enum n) :=
      funext fun n => (multiCorr_eq_integral S hAamb t _).symm
    rw [hfun] at h
    exact h

end MPS

end CantorSzemeredi

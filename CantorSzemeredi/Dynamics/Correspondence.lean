/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Basic
import CantorSzemeredi.Dynamics.SymbolicModel

/-!
# Furstenberg correspondence principle

Blueprint: `blueprint/src/chapter/structure.tex`, Theorem `thm:furstenberg-correspondence`.
-/

namespace CantorSzemeredi

open MeasureTheory MPS Filter
open scoped Classical ENNReal

/-! ### Shifting by an integer -/

private def shiftBy (n : ℤ) (ω : ℤ → Fin 2) : ℤ → Fin 2 := fun k => ω (k + n)

private theorem continuous_shiftBy (n : ℤ) : Continuous (shiftBy n) :=
  continuous_pi fun k => continuous_apply (k + n)

private theorem shiftBy_mem_symbolicSet_iff (A : Set ℤ) (n : ℤ) :
    shiftBy n (fun k => if k ∈ A then (1 : Fin 2) else 0) ∈ symbolicSet ↔ n ∈ A := by
  simp only [symbolicSet, Set.mem_ofPred_eq, shiftBy, zero_add]
  split_ifs with h <;> simp [h]

private theorem shiftBy_mem_preimage_iff (A : Set ℤ) (n r : ℤ) :
    shiftBy n (fun k => if k ∈ A then (1 : Fin 2) else 0) ∈
      shiftBy r ⁻¹' symbolicSet ↔ n + r ∈ A := by
  simp only [Set.mem_preimage, symbolicSet, Set.mem_ofPred_eq, shiftBy, zero_add]
  have hrn : r + n = n + r := add_comm r n
  rw [hrn]
  split_ifs with h <;> simp [h]

/-! ### Clopen properties -/

private theorem isClopen_symbolicSet : IsClopen symbolicSet :=
  (isClopen_discrete ({1} : Set (Fin 2))).preimage (continuous_apply 0)

private theorem isClopen_iInter_shiftBy_preimage (R : Finset ℤ) :
    IsClopen (⋂ r ∈ R, shiftBy r ⁻¹' symbolicSet) :=
  isClopen_biInter_finset fun r _ => isClopen_symbolicSet.preimage (continuous_shiftBy r)

/-! ### Iterate of `symbolicShift.symm` -/

private theorem symbolicShift_symm_iterate (m : ℕ) (ω : ℤ → Fin 2) (k : ℤ) :
    (⇑symbolicShift.symm)^[m] ω k = ω (k - ↑m) := by
  induction m generalizing ω k with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ, Function.comp_apply, ih]
    change ω ((k - ↑m) - 1) = ω (k - ↑(m + 1))
    congr 1; push_cast; ring

/-! ### Shift composition -/

private theorem symbolicShift_comp_shiftBy (n : ℤ) (ω : ℤ → Fin 2) :
    symbolicShift (shiftBy n ω) = shiftBy (n + 1) ω := by
  funext k; show ω ((k + 1) + n) = ω (k + (n + 1)); ring_nf

/-! ### Telescoping for ℤ-indexed sums -/

private lemma sum_Ico_sub_int (f : ℤ → ℝ) (m n : ℤ) (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, (f (i + 1) - f i) = f n - f m := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = m + k := ⟨(n - m).toNat, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have hmk : m ≤ m + ↑k := by omega
    have hsplit : Finset.Ico m (m + (↑(k + 1) : ℤ)) = Finset.Ico m (m + ↑k) ∪ {m + ↑k} := by
      ext x; simp [Finset.mem_Ico]; omega
    rw [hsplit, Finset.sum_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.sum_singleton, ih hmk]
    have : m + (↑(k + 1) : ℤ) = m + ↑k + 1 := by push_cast; ring
    rw [this]; ring

/-! ### The core construction: invariant measure via compactness -/

instance : uniformFilterInt.IsCountablyGenerated :=
  uniformFilterInt_hasBasis.isCountablyGenerated

private theorem furstenberg_measure (A : Set ℤ) (hA : 0 < upperBanachDensity A) :
    ∃ μ : Measure (ℤ → Fin 2),
      IsProbabilityMeasure μ ∧
      MeasurePreserving symbolicShift μ μ ∧
      (μ symbolicSet).toReal = upperBanachDensity A ∧
      ∀ R : Finset ℤ,
        (μ (⋂ r ∈ R, shiftBy r ⁻¹' symbolicSet)).toReal ≤
          upperBanachDensity (⋂ r ∈ R, (· + r) ⁻¹' A) := by
  -- The indicator function
  let ω_A : ℤ → Fin 2 := fun k => if k ∈ A then 1 else 0
  -- Step 1: Extract a sequence realizing the upper Banach density.
  let dens : ℤ × ℤ → ℝ := fun p =>
    (((Finset.Ico p.1 p.2).filter (· ∈ A)).card : ℝ) / (p.2 - p.1 : ℤ)
  have hdens_nonneg : ∀ p : ℤ × ℤ, 0 ≤ dens p := by
    intro ⟨M, N⟩; simp only [dens]
    by_cases h : M < N
    · exact div_nonneg (Nat.cast_nonneg _)
        (by exact_mod_cast (show (0 : ℤ) ≤ N - M by omega))
    · have : Finset.Ico M N = ∅ := Finset.Ico_eq_empty h
      simp [this]
  have hdens_bdd : IsBoundedUnder (· ≤ ·) uniformFilterInt dens := by
    refine ⟨1, uniformFilterInt_hasBasis.eventually_iff.2 ⟨1, trivial, fun p hp => ?_⟩⟩
    show dens p ≤ 1; simp only [dens]
    have hp' : (1 : ℤ) ≤ p.2 - p.1 := hp
    have hle : p.1 ≤ p.2 := by omega
    have hpos : (0 : ℝ) < ((p.2 - p.1 : ℤ) : ℝ) := by exact_mod_cast (show (0 : ℤ) < p.2 - p.1 by omega)
    rw [div_le_one hpos]
    have h1 : (((Finset.Ico p.1 p.2).filter (· ∈ A)).card : ℤ) ≤ p.2 - p.1 :=
      (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans
        (Int.card_Ico_of_le p.1 p.2 hle).le
    exact_mod_cast h1
  have hdens_cobdd : IsCoboundedUnder (· ≤ ·) uniformFilterInt dens :=
    .of_frequently_ge ((Eventually.of_forall hdens_nonneg).frequently)
  obtain ⟨x, hx_lim, hx_cofinal⟩ := exists_seq_tendsto_limsup hdens_cobdd hdens_bdd
  have hx_lim' : Tendsto (dens ∘ x) atTop (nhds (upperBanachDensity A)) := hx_lim
  -- Step 2: Build empirical probability measures.
  have hMN : ∀ᶠ k in atTop, (x k).1 < (x k).2 :=
    (hx_cofinal.eventually (uniformFilterInt_hasBasis.eventually_iff.2
      ⟨1, trivial, fun p (hp : (1 : ℤ) ≤ p.2 - p.1) => by omega⟩)).mono
      fun _ hk => by omega
  let ν_raw : ℕ → Measure (ℤ → Fin 2) := fun k =>
    if (x k).1 < (x k).2 then
      ((Finset.Ico (x k).1 (x k).2).card : ℝ≥0∞)⁻¹ •
        ∑ n ∈ Finset.Ico (x k).1 (x k).2, Measure.dirac (shiftBy n ω_A)
    else Measure.dirac ω_A
  have hν_prob : ∀ k, IsProbabilityMeasure (ν_raw k) := by
    intro k; simp only [ν_raw]
    split
    · next h =>
      constructor
      rw [Measure.smul_apply, Measure.finsetSum_apply]
      simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const,
        nsmul_eq_mul, mul_one]
      exact ENNReal.inv_mul_cancel
        (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr
          ⟨(x k).1, Finset.mem_Ico.mpr ⟨le_refl _, h⟩⟩).ne')
        (ENNReal.natCast_ne_top _)
    · exact inferInstance
  let ν : ℕ → ProbabilityMeasure (ℤ → Fin 2) := fun k => ⟨ν_raw k, hν_prob k⟩
  -- Step 3: Extract convergent subsequence via Prokhorov.
  obtain ⟨μ_pm, -, φ, hφ_mono, hconv⟩ :=
    isCompact_univ.tendsto_subseq (fun k => Set.mem_univ (ν k))
  let μ := (μ_pm : Measure (ℤ → Fin 2))
  haveI : IsProbabilityMeasure μ := inferInstance
  -- Helper: empirical measure of a measurable set, converted to ℝ
  have hν_toReal : ∀ k, (x k).1 < (x k).2 → ∀ (E : Set (ℤ → Fin 2)), MeasurableSet E →
      ((ν k) E : ℝ) = (((Finset.Ico (x k).1 (x k).2).filter
        (fun n => shiftBy n ω_A ∈ E)).card : ℝ) /
        ((x k).2 - (x k).1 : ℤ) := by
    intro k hk E hE
    have hν_eq : ν_raw k = ((Finset.Ico (x k).1 (x k).2).card : ℝ≥0∞)⁻¹ •
        ∑ n ∈ Finset.Ico (x k).1 (x k).2, Measure.dirac (shiftBy n ω_A) := if_pos hk
    change (ν_raw k E).toReal = _
    rw [hν_eq, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
    simp_rw [Measure.dirac_apply' _ hE, Set.indicator_apply, Pi.one_apply]
    rw [Finset.sum_boole, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast, inv_mul_eq_div]
    congr 1
    have h1 := Int.card_Ico (x k).1 (x k).2
    rw [h1]
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ (x k).2 - (x k).1 by omega)
  -- Step 4: Shift-invariance via Krylov-Bogolyubov.
  have hcp : MapClusterPt μ_pm atTop ν := by
    have h1 : ClusterPt μ_pm (Filter.map ν (Filter.map φ atTop)) := by
      rw [Filter.map_map]; exact hconv.mapClusterPt
    exact h1.mono (Filter.map_mono hφ_mono.tendsto_atTop)
  have hinv : MeasurePreserving symbolicShift μ μ := by
    refine ⟨symbolicShift.continuous.measurable, ?_⟩
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro g
    rw [integral_map symbolicShift.continuous.aemeasurable g.continuous.aestronglyMeasurable]
    apply ProbabilityMeasure.integral_comp_eq_integral_of_mapClusterPt
      symbolicShift.continuous hcp
    have hL_atTop : Tendsto (fun k => (((x k).2 - (x k).1 : ℤ) : ℝ)) atTop atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      obtain ⟨n, hn⟩ : ∃ n : ℕ, b ≤ (n : ℝ) := ⟨⌈b⌉₊, Nat.le_ceil b⟩
      have hmem : ∀ᶠ k in atTop, (n : ℤ) ≤ (x k).2 - (x k).1 :=
        hx_cofinal.eventually (uniformFilterInt_hasBasis.eventually_iff.2
          ⟨n, trivial, fun p hp => hp⟩)
      filter_upwards [hmem] with k hk
      calc b ≤ (n : ℝ) := hn
        _ = ((n : ℤ) : ℝ) := by push_cast; ring
        _ ≤ (((x k).2 - (x k).1 : ℤ) : ℝ) := Int.cast_le.mpr hk
    set bound : ℕ → ℝ := fun k => (((x k).2 - (x k).1 : ℤ) : ℝ)⁻¹ * (2 * ‖g‖) with hbound_def
    have hbound_lim : Tendsto bound atTop (nhds 0) := by
      rw [show (0 : ℝ) = 0 * (2 * ‖g‖) from (zero_mul _).symm]
      exact (tendsto_inv_atTop_zero.comp hL_atTop).mul tendsto_const_nhds
    apply squeeze_zero_norm' _ hbound_lim
    filter_upwards [hMN] with k hk
    have hν_eq : ν_raw k = ((Finset.Ico (x k).1 (x k).2).card : ℝ≥0∞)⁻¹ •
        ∑ n ∈ Finset.Ico (x k).1 (x k).2, Measure.dirac (shiftBy n ω_A) := if_pos hk
    have hL : (0 : ℝ) < ((x k).2 - (x k).1 : ℤ) := by exact_mod_cast show (0 : ℤ) < _ by omega
    have hcard_eq : ((Finset.Ico (x k).1 (x k).2).card : ℝ) = ((x k).2 - (x k).1 : ℤ) := by
      rw [Int.card_Ico]
      exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ (x k).2 - (x k).1 by omega)
    let σ_cont : C(ℤ → Fin 2, ℤ → Fin 2) := ⟨symbolicShift, symbolicShift.continuous⟩
    let gs := g.compContinuous σ_cont
    have hint_g : ∫ y, g y ∂(ν_raw k) =
        ((Finset.Ico (x k).1 (x k).2).card : ℝ)⁻¹ *
        ∑ n ∈ Finset.Ico (x k).1 (x k).2, g (shiftBy n ω_A) := by
      rw [hν_eq, integral_smul_measure, smul_eq_mul,
        integral_finsetSum_measure (fun i _ => g.integrable _)]
      simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    have hgs_eq : ∀ n, gs (shiftBy n ω_A) = g (shiftBy (n + 1) ω_A) := fun n => by
      show g (symbolicShift (shiftBy n ω_A)) = g (shiftBy (n + 1) ω_A)
      rw [symbolicShift_comp_shiftBy]
    have hint_gs : ∫ y, gs y ∂(ν_raw k) =
        ((Finset.Ico (x k).1 (x k).2).card : ℝ)⁻¹ *
        ∑ n ∈ Finset.Ico (x k).1 (x k).2, g (shiftBy (n + 1) ω_A) := by
      rw [hν_eq, integral_smul_measure, smul_eq_mul,
        integral_finsetSum_measure (fun i _ => gs.integrable _)]
      simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      congr 1
      exact Finset.sum_congr rfl fun n _ => hgs_eq n
    have hdiff : ∫ y, gs y ∂(ν_raw k) - ∫ y, g y ∂(ν_raw k) =
        (((x k).2 - (x k).1 : ℤ) : ℝ)⁻¹ *
        (g (shiftBy (x k).2 ω_A) - g (shiftBy (x k).1 ω_A)) := by
      rw [hint_gs, hint_g, ← mul_sub, ← Finset.sum_sub_distrib,
        sum_Ico_sub_int (fun n => g (shiftBy n ω_A)) _ _ hk.le, hcard_eq]
    show ‖(∫ y, (⇑g ∘ ⇑symbolicShift) y ∂↑(ν k)) - ∫ y, g y ∂↑(ν k)‖ ≤ bound k
    rw [show (∫ y, (⇑g ∘ ⇑symbolicShift) y ∂↑(ν k)) - ∫ y, g y ∂↑(ν k) =
        ∫ y, gs y ∂(ν_raw k) - ∫ y, g y ∂(ν_raw k) from rfl, hdiff, hbound_def,
      norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hL))]
    exact mul_le_mul_of_nonneg_left
      (calc ‖(g (shiftBy (x k).2 ω_A) : ℝ) - g (shiftBy (x k).1 ω_A)‖
          ≤ ‖(g (shiftBy (x k).2 ω_A) : ℝ)‖ + ‖(g (shiftBy (x k).1 ω_A) : ℝ)‖ :=
            norm_sub_le _ _
        _ ≤ ‖g‖ + ‖g‖ :=
            add_le_add (g.norm_coe_le_norm _) (g.norm_coe_le_norm _)
        _ = 2 * ‖g‖ := by ring)
      (inv_nonneg.mpr (le_of_lt hL))
  -- Step 5: Density equality.
  have hdens_eq : (μ symbolicSet).toReal = upperBanachDensity A := by
    have hport := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
      hconv isClopen_symbolicSet
    have hport_real := NNReal.continuous_coe.continuousAt.tendsto.comp hport
    have hdens_sub : Tendsto (fun k => dens (x (φ k))) atTop
        (nhds (upperBanachDensity A)) :=
      hx_lim'.comp hφ_mono.tendsto_atTop
    have heq : ∀ᶠ k in atTop, ((ν (φ k)) symbolicSet : ℝ) = dens (x (φ k)) := by
      filter_upwards [hφ_mono.tendsto_atTop.eventually hMN] with k hk
      rw [hν_toReal (φ k) hk _ measurableSet_symbolicSet]
      simp only [dens]
      rw [Finset.filter_congr fun n _ => shiftBy_mem_symbolicSet_iff A n]
    exact tendsto_nhds_unique ((tendsto_congr' heq).mp hport_real) hdens_sub
  -- Step 6: Inequality for intersections.
  have hineq : ∀ R : Finset ℤ,
      (μ (⋂ r ∈ R, shiftBy r ⁻¹' symbolicSet)).toReal ≤
        upperBanachDensity (⋂ r ∈ R, (· + r) ⁻¹' A) := by
    intro R
    set B := ⋂ r ∈ R, (· + r) ⁻¹' A
    set E := ⋂ r ∈ R, shiftBy r ⁻¹' symbolicSet
    have hE_clopen := isClopen_iInter_shiftBy_preimage R
    have hmem_iff : ∀ n, shiftBy n ω_A ∈ E ↔ n ∈ B := by
      intro n
      simp only [E, B, Set.mem_iInter, Set.mem_preimage]
      exact forall₂_congr fun r _ => shiftBy_mem_preimage_iff A n r
    have hport := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hconv hE_clopen
    have hport_real := NNReal.continuous_coe.continuousAt.tendsto.comp hport
    have heq : ∀ᶠ k in atTop, ((ν (φ k)) E : ℝ) =
        (((Finset.Ico (x (φ k)).1 (x (φ k)).2).filter (· ∈ B)).card : ℝ) /
        ((x (φ k)).2 - (x (φ k)).1 : ℤ) := by
      filter_upwards [hφ_mono.tendsto_atTop.eventually hMN] with k hk
      rw [hν_toReal (φ k) hk E hE_clopen.1.measurableSet,
        show Finset.filter (fun n => shiftBy n ω_A ∈ E) (Finset.Ico (x (φ k)).1 (x (φ k)).2) =
          Finset.filter (· ∈ B) (Finset.Ico (x (φ k)).1 (x (φ k)).2) from
          Finset.filter_congr fun n _ => hmem_iff n]
    have htend : Tendsto (fun k =>
        (((Finset.Ico (x (φ k)).1 (x (φ k)).2).filter (· ∈ B)).card : ℝ) /
        ((x (φ k)).2 - (x (φ k)).1 : ℤ)) atTop (nhds (μ E).toReal) :=
      (tendsto_congr' heq).mp hport_real
    have hbdd : Filter.IsBoundedUnder (· ≤ ·) uniformFilterInt
        (fun p : ℤ × ℤ => (((Finset.Ico p.1 p.2).filter (· ∈ B)).card : ℝ) /
          (p.2 - p.1 : ℤ)) := by
      refine ⟨1, ?_⟩
      rw [Filter.eventually_map]
      apply Filter.Eventually.of_forall
      intro p
      dsimp only
      by_cases h : p.1 < p.2
      · have hpos : (0 : ℝ) < ((p.2 - p.1 : ℤ) : ℝ) := by exact_mod_cast show (0 : ℤ) < _ by omega
        rw [div_le_one hpos]
        calc (((Finset.Ico p.1 p.2).filter (· ∈ B)).card : ℝ)
            ≤ ((Finset.Ico p.1 p.2).card : ℝ) := Nat.cast_le.mpr (Finset.card_filter_le _ _)
          _ = ((p.2 - p.1 : ℤ) : ℝ) := by
              rw [Int.card_Ico]; exact_mod_cast Int.toNat_of_nonneg (show (0 : ℤ) ≤ _ by omega)
      · rw [show (Finset.Ico p.1 p.2 : Finset ℤ) = ∅ from Finset.Ico_eq_empty h,
            Finset.filter_empty, Finset.card_empty, Nat.cast_zero, zero_div]
        norm_num
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hev : ∀ᶠ p in uniformFilterInt,
        (((Finset.Ico p.1 p.2).filter (· ∈ B)).card : ℝ) / (p.2 - p.1 : ℤ) <
        upperBanachDensity B + ε / 2 :=
      Filter.eventually_lt_of_limsup_lt (show upperBanachDensity B < _ by linarith) hbdd
    have hev' := (hx_cofinal.comp hφ_mono.tendsto_atTop).eventually hev
    linarith [le_of_tendsto htend (hev'.mono fun k hk => le_of_lt hk)]
  exact ⟨μ, inferInstance, hinv, hdens_eq, hineq⟩

/-- **Theorem `thm:furstenberg-correspondence`** (Furstenberg correspondence principle). -/
theorem furstenberg_correspondence (A : Set ℤ) (hA : 0 < upperBanachDensity A) :
    ∃ (S : MPS.{0}) (B : Set S.X),
      MeasurableSet B ∧
      (S.m B).toReal = upperBanachDensity A ∧
      ∀ (R : Finset ℤ),
        upperBanachDensity (⋂ r ∈ R, (· + r) ⁻¹' A) ≥
          (S.m (⋂ r ∈ R, S.iter r ⁻¹' B)).toReal := by
  obtain ⟨μ, hμ_prob, hμ_inv, hμ_density, hμ_ineq⟩ := furstenberg_measure A hA
  have := hμ_prob
  set S : MPS.{0} := {
    X := ℤ → Fin 2
    m := μ
    T := symbolicShift
    measurableEquiv := symbolicShift.toMeasurableEquiv
    coe_measurableEquiv := rfl
    measurePreserving := hμ_inv
  } with hS_def
  refine ⟨S, symbolicSet, measurableSet_symbolicSet, hμ_density, fun R => ?_⟩
  suffices h : ∀ r : ℤ, S.iter r ⁻¹' symbolicSet = shiftBy r ⁻¹' symbolicSet by
    simp_rw [h]; exact hμ_ineq R
  intro r
  ext ω
  simp only [Set.mem_preimage]
  show (S.iter r ω) 0 = 1 ↔ ω (0 + r) = 1
  have heq : (S.iter r ω) 0 = ω (0 + r) := by
    cases r with
    | ofNat m =>
      change (⇑symbolicShift)^[m] ω 0 = ω (0 + ↑m)
      exact symbolicShift_iterate m ω 0
    | negSucc m =>
      change (⇑(symbolicShift.toMeasurableEquiv.symm))^[m + 1] ω 0 = ω (0 + Int.negSucc m)
      simp only [Homeomorph.toMeasurableEquiv_symm_coe, symbolicShift_symm_iterate]
      congr 1
  rw [heq]

end CantorSzemeredi

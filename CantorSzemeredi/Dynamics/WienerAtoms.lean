/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.Spectral

/-!
# Wiener's lemma: the atoms of the spectral measure

Blueprint: `blueprint/src/chapter/mps.tex`, `lem:wiener`.

The Cesàro means of `|σ̂(n)|²` converge to the measure of the diagonal under `σ × σ`, and this
equals the sum of the squared atom sizes `∑_θ σ({θ})²`.  Consequently `σ` is atomless if and only
if these Cesàro means tend to `0`.  The file proves the sum identity; the limit statement and the
converse are in `Spectral.lean`.
-/

namespace CantorSzemeredi

open MeasureTheory Filter Topology

variable {σ : Measure Torus} [IsFiniteMeasure σ]

/-- There are only countably many atoms. -/
theorem countable_atoms : Set.Countable {θ : Torus | 0 < σ {θ}} :=
  Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top σ
    (fun θ => measurableSet_singleton θ)
    (fun _ _ h => Set.disjoint_singleton.2 h)
    (by simp [measure_ne_top])

/-- The integral of the atom sizes is the sum of their squares. -/
theorem lintegral_atom_sq :
    ∫⁻ α, σ {α} ∂σ = ∑' θ : Torus, σ {θ} * σ {θ} := by
  set A : Set Torus := {θ : Torus | 0 < σ {θ}} with hA_def
  have : Countable A := countable_atoms.to_subtype
  -- `σ{α}` is the sum over the countably many atoms of their indicators.
  have hpt : ∀ α : Torus, σ {α} = ∑' θ : A,
      Set.indicator {(θ : Torus)} (fun _ => σ {(θ : Torus)}) α := by
    intro α
    by_cases hα : α ∈ A
    · rw [tsum_eq_single (⟨α, hα⟩ : A)]
      · simp
      · intro θ hθ
        have hne : (θ : Torus) ≠ α := fun h => hθ (Subtype.ext h)
        simp [Set.indicator_of_notMem (show α ∉ ({(θ : Torus)} : Set Torus) from
          fun h => hne (Set.mem_singleton_iff.1 h).symm)]
    · have hzero : σ {α} = 0 := by
        have : ¬ 0 < σ {α} := fun h => hα h
        exact le_antisymm (not_lt.1 this) ((by positivity))
      rw [hzero]
      symm
      refine ENNReal.tsum_eq_zero.2 fun θ => ?_
      have hne : (θ : Torus) ≠ α := fun h => hα (h ▸ θ.2)
      rw [Set.indicator_of_notMem (show α ∉ ({(θ : Torus)} : Set Torus) from
        fun h => hne (Set.mem_singleton_iff.1 h).symm)]
  calc ∫⁻ α, σ {α} ∂σ
      = ∫⁻ α, ∑' θ : A, Set.indicator {(θ : Torus)} (fun _ => σ {(θ : Torus)}) α ∂σ :=
        lintegral_congr fun α => hpt α
    _ = ∑' θ : A, ∫⁻ α, Set.indicator {(θ : Torus)} (fun _ => σ {(θ : Torus)}) α ∂σ :=
        lintegral_tsum fun θ => (measurable_const.indicator
          (measurableSet_singleton _)).aemeasurable
    _ = ∑' θ : A, σ {(θ : Torus)} * σ {(θ : Torus)} := by
        refine tsum_congr fun θ => ?_
        rw [lintegral_indicator_const (measurableSet_singleton _)]
    _ = ∑' θ : Torus, σ {θ} * σ {θ} := by
        rw [tsum_subtype A (fun θ => σ {θ} * σ {θ})]
        refine tsum_congr fun θ => ?_
        by_cases hθ : θ ∈ A
        · rw [Set.indicator_of_mem hθ]
        · rw [Set.indicator_of_notMem hθ]
          have : σ {θ} = 0 := le_antisymm (not_lt.1 hθ) ((by positivity))
          simp [this]

/-- **Wiener's lemma, sum form.**  The Cesàro limit of `|σ̂(n)|²` is the sum of the squared atom
sizes. -/
theorem tendsto_cesaro_sq_atoms :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ‖sigmaHat σ (n : ℤ)‖ ^ 2 : ℝ))
      atTop (𝓝 (∑' θ : Torus, (σ {θ}).toReal ^ 2)) := by
  have hsum : ∑' θ : Torus, (σ {θ}).toReal ^ 2 = ((σ.prod σ) {q : Torus × Torus | q.1 = q.2}).toReal := by
    rw [prod_diagonal_eq_lintegral, lintegral_atom_sq, ENNReal.tsum_toReal_eq]
    · refine tsum_congr fun θ => ?_
      rw [ENNReal.toReal_mul, sq]
    · intro θ
      exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [hsum]
  exact tendsto_cesaro_sq_norm_sigmaHat

/-- **Wiener's lemma (`lem:wiener`), the atomless form.**  The measure `σ` has no atoms if and
only if the Cesàro means of `|σ̂(n)|²` tend to `0`. -/
theorem noAtoms_iff_tendsto_cesaro_zero :
    (∀ θ : Torus, σ {θ} = 0) ↔
      Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ‖sigmaHat σ (n : ℤ)‖ ^ 2 : ℝ))
        atTop (𝓝 0) := by
  constructor
  · intro h
    have hzero : ∑' θ : Torus, (σ {θ}).toReal ^ 2 = 0 := by
      simp [h]
    have := tendsto_cesaro_sq_atoms (σ := σ)
    rwa [hzero] at this
  · intro h θ
    exact noAtoms_of_tendsto_cesaro_zero h θ

end CantorSzemeredi

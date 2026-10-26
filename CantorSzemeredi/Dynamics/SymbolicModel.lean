/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.CSZ

/-!
# Symbolic model

Blueprint: `blueprint/src/chapter/structure.tex`, Lemma `lem:symbolic-model`.

Given an MPS `(X, 𝒜, m, T)` and a measurable set `A`, the *symbolic model* is the MPS
`(Ω, ℬ, μ, τ)` where `Ω = {0,1}^ℤ`, `τ` is the left shift, `Φ(x)(n) = 𝟙_A(T^n x)` is the
coding map, and `μ = Φ_∗ m`.  The key output is that multicorrelations in the original system
match those in the symbolic model.
-/

namespace CantorSzemeredi

open MeasureTheory
open scoped Classical

namespace MPS

/-! ### The shift homeomorphism -/

noncomputable def symbolicShift : (ℤ → Fin 2) ≃ₜ (ℤ → Fin 2) where
  toFun ω n := ω (n + 1)
  invFun ω n := ω (n - 1)
  left_inv ω := by ext n; simp [sub_add_cancel]
  right_inv ω := by ext n; simp [add_sub_cancel_right]
  continuous_toFun := continuous_pi fun n => continuous_apply (n + 1)
  continuous_invFun := continuous_pi fun n => continuous_apply (n - 1)

lemma symbolicShift_apply (ω : ℤ → Fin 2) (n : ℤ) :
    symbolicShift ω n = ω (n + 1) := rfl

lemma symbolicShift_iterate (k : ℕ) (ω : ℤ → Fin 2) (n : ℤ) :
    symbolicShift^[k] ω n = ω (n + ↑k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_def]
    change (⇑symbolicShift)^[k] ω (n + 1) = ω (n + ↑(k + 1))
    rw [ih]; congr 1; push_cast; ring

/-! ### The coding map -/

noncomputable def codingMap (S : MPS) (A : Set S.X) (x : S.X) : ℤ → Fin 2 :=
  fun n => if ((S.measurableEquiv.toEquiv ^ n : Equiv.Perm S.X) x) ∈ A then 1 else 0

lemma measurable_zpow (S : MPS) (n : ℤ) :
    Measurable (⇑(S.measurableEquiv.toEquiv ^ n : Equiv.Perm S.X)) := by
  cases n with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast, Equiv.Perm.coe_pow,
      MeasurableEquiv.coe_toEquiv, S.coe_measurableEquiv]
    exact S.measurable_T.iterate k
  | negSucc k =>
    rw [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow]
    have : (⇑(S.measurableEquiv.toEquiv⁻¹ : Equiv.Perm S.X) : S.X → S.X) = S.Tinv := by
      ext x; simp [MPS.Tinv, Equiv.Perm.inv_def]
    rw [this]; exact S.measurable_Tinv.iterate (k + 1)

lemma measurable_codingMap (S : MPS) {A : Set S.X} (hA : MeasurableSet A) :
    Measurable (codingMap S A) := by
  apply measurable_pi_iff.mpr; intro n
  exact Measurable.ite (S.measurable_zpow n hA) measurable_const measurable_const

lemma perm_zpow_natCast_eq_iterate (S : MPS) (k : ℕ) (x : S.X) :
    (S.measurableEquiv.toEquiv ^ (↑k : ℤ) : Equiv.Perm S.X) x = S.T^[k] x := by
  rw [zpow_natCast, Equiv.Perm.coe_pow]
  change (⇑S.measurableEquiv.toEquiv)^[k] x = S.T^[k] x
  congr 1; rw [MeasurableEquiv.coe_toEquiv, S.coe_measurableEquiv]

/-! ### Intertwining: `Φ ∘ T = τ ∘ Φ` -/

lemma codingMap_comp_T (S : MPS) (A : Set S.X) :
    codingMap S A ∘ S.T = symbolicShift ∘ codingMap S A := by
  funext x n
  simp only [Function.comp_apply, codingMap, symbolicShift_apply]
  congr 1
  have : (S.measurableEquiv.toEquiv ^ n : Equiv.Perm S.X) (S.T x) =
      (S.measurableEquiv.toEquiv ^ (n + 1) : Equiv.Perm S.X) x := by
    rw [zpow_add, zpow_one, Equiv.Perm.mul_apply,
      MeasurableEquiv.coe_toEquiv, S.coe_measurableEquiv]
  exact propext (by rw [this])

/-! ### The symbolic set `{ω : ω(0) = 1}` -/

def symbolicSet : Set (ℤ → Fin 2) := {ω | ω 0 = 1}

lemma measurableSet_symbolicSet : MeasurableSet symbolicSet :=
  measurable_pi_apply 0 (measurableSet_singleton 1)

/-! ### Preimage identity -/

lemma preimage_codingMap_shift (S : MPS) (A : Set S.X) (k : ℕ) :
    codingMap S A ⁻¹' (symbolicShift^[k] ⁻¹' symbolicSet) = S.T^[k] ⁻¹' A := by
  ext x
  simp only [Set.mem_preimage, symbolicSet, Set.mem_ofPred_eq]
  rw [symbolicShift_iterate k _ 0, zero_add, codingMap, perm_zpow_natCast_eq_iterate]
  split_ifs with h <;> simp [h]

/-! ### The symbolic model MPS -/

noncomputable def symbolicModel (S : MPS) {A : Set S.X} (hA : MeasurableSet A) : MPS where
  X := ℤ → Fin 2
  m := Measure.map (codingMap S A) S.m
  T := symbolicShift
  measurableEquiv := symbolicShift.toMeasurableEquiv
  coe_measurableEquiv := rfl
  measurePreserving := by
    have hΦ := S.measurable_codingMap hA
    refine ⟨symbolicShift.continuous.measurable, ?_⟩
    rw [Measure.map_map symbolicShift.continuous.measurable hΦ, ← codingMap_comp_T,
      ← Measure.map_map hΦ S.measurable_T, S.measurePreserving.map_eq]

/-! ### Multicorrelation identity -/

theorem multiCorr_symbolicModel (S : MPS) {A : Set S.X} (hA : MeasurableSet A)
    (t d : ℕ) :
    (S.symbolicModel hA).multiCorr symbolicSet t d = S.multiCorr A t d := by
  dsimp only [multiCorr, symbolicModel]
  congr 1
  have hmeas : MeasurableSet
      (⋂ s ∈ Finset.range (t + 1), symbolicShift^[s * d] ⁻¹' symbolicSet) :=
    .biInter (Finset.countable_toSet _) fun s _ =>
      (symbolicShift.toMeasurableEquiv.measurable.iterate (s * d)) measurableSet_symbolicSet
  rw [Measure.map_apply (S.measurable_codingMap hA) hmeas, Set.preimage_iInter₂]
  simp_rw [preimage_codingMap_shift]

end MPS

end CantorSzemeredi

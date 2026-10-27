/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.Structure
import CantorSzemeredi.Dynamics.Correspondence

/-!
# Main theorems

Blueprint: `blueprint/src/chapter/overview.tex`, Theorems `thm:main-ergodic` and
`thm:main-integers`.
-/

namespace CantorSzemeredi

open MeasureTheory MPS

/-- A superset of a syndetic set is syndetic. -/
theorem Syndetic.mono {A B : Set ℕ} (hA : Syndetic A) (hAB : A ⊆ B) : Syndetic B := by
  obtain ⟨L, hL⟩ := hA
  exact ⟨L, fun n => let ⟨k, hk, h1, h2⟩ := hL n; ⟨k, hAB hk, h1, h2⟩⟩

/-- **Theorem `thm:main-ergodic`.**  The case `i = 0` of the CSZ property for the full
σ-algebra: every MPS has positive uniform liminf of multiple correlations along any Cantor
enumeration. -/
theorem main_ergodic (C : CantorData) (S : MPS) (A : Set S.X)
    (hA : MeasurableSet A) (hpos : 0 < S.m A) (t : ℕ) (ht : 1 ≤ t) :
    0 < uniformLiminf fun n => S.multiCorr A t (C.enum n) := by
  have h := CSZ_of_forall_ergodic_CSZ
    (fun R inst herg => @CSZ_of_ergodic R inst herg) S C A hA hpos t ht 0
  simp only [pow_zero, one_mul] at h
  exact h

/-- **Theorem `thm:main-integers`.**  Szemerédi's theorem along Cantor sets of integers.
For every `A ⊆ ℤ` of positive upper Banach density and every `t ≥ 1`, the set of indices
`{n | d*(A ∩ (A − kₙ) ∩ ⋯ ∩ (A − t·kₙ)) > 0}` is syndetic. -/
theorem main_integers (C : CantorData) (A : Set ℤ) (hA : 0 < upperBanachDensity A)
    (t : ℕ) (ht : 1 ≤ t) :
    Syndetic {n : ℕ | 0 < upperBanachDensity
      (⋂ j ∈ Finset.range (t + 1), (· + (↑(j * C.enum n) : ℤ)) ⁻¹' A)} := by
  obtain ⟨S, B, hBm, hBdens, hBineq⟩ := furstenberg_correspondence A hA
  have hpos : 0 < S.m B := by
    by_contra h; simp only [not_lt] at h
    have h0 : S.m B = 0 := le_antisymm h (by positivity)
    simp [h0] at hBdens; linarith
  apply (syndetic_of_uniformLiminf_pos (fun n => S.multiCorr_nonneg B t (C.enum n))
    (main_ergodic C S B hBm hpos t ht)).mono
  intro n hn
  suffices h : upperBanachDensity (⋂ j ∈ Finset.range (t + 1),
      (· + (↑(j * C.enum n) : ℤ)) ⁻¹' A) ≥ S.multiCorr B t (C.enum n) by
    exact lt_of_lt_of_le hn h
  let R := (Finset.range (t + 1)).image (fun j : ℕ => (↑(j * C.enum n) : ℤ))
  have hA_eq : (⋂ r ∈ R, (· + r) ⁻¹' A) =
      ⋂ j ∈ Finset.range (t + 1), (· + (↑(j * C.enum n) : ℤ)) ⁻¹' A := by
    ext x; simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h j hj; exact h _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    · intro h r hr
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
      exact h j hj
  have hR_iter : (⋂ r ∈ R, S.iter r ⁻¹' B) =
      ⋂ s ∈ Finset.range (t + 1), (S.T^[s * C.enum n]) ⁻¹' B := by
    ext x; simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h s hs; exact h _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    · intro h r hr
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
      exact h s hs
  calc upperBanachDensity (⋂ j ∈ Finset.range (t + 1),
        (· + (↑(j * C.enum n) : ℤ)) ⁻¹' A)
      = upperBanachDensity (⋂ r ∈ R, (· + r) ⁻¹' A) := by rw [hA_eq]
    _ ≥ (S.m (⋂ r ∈ R, S.iter r ⁻¹' B)).toReal := hBineq R
    _ = S.multiCorr B t (C.enum n) := congrArg (fun s => (S.m s).toReal) hR_iter

end CantorSzemeredi

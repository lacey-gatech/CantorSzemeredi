/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.VdW.Cvdw

/-!
# Infinite colourings

Blueprint: `blueprint/src/chapter/vdw.tex`, `lem:vdw-infinite`.  Every colouring `χ : ℕ → Fin L` has a
monochromatic progression with common difference in `Cantor \ {0}`.  The colourings form the
compact space `(Fin L)^ℕ` with the one-sided shift; the closure of the forward orbit of `χ` is a
topological dynamical system, and the dynamical form of the theorem applies to the colour cover.
-/

namespace CantorSzemeredi

open Set Finset Filter Topology

/-- The one-sided shift on sequences. -/
def leftShift {L : ℕ} (η : ℕ → Fin L) : ℕ → Fin L := fun n => η (n + 1)

theorem continuous_leftShift {L : ℕ} : Continuous (fun η : ℕ → Fin L => leftShift η) :=
  continuous_pi fun n => continuous_apply (n + 1)

theorem leftShift_iterate {L : ℕ} (n : ℕ) (η : ℕ → Fin L) (k : ℕ) :
    (fun ζ : ℕ → Fin L => leftShift ζ)^[n] η k = η (k + n) := by
  induction n generalizing η k with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [leftShift, Nat.add_assoc]

/-- **Lemma `lem:vdw-infinite`.**  Every colouring `χ : ℕ → Fin L` has a monochromatic progression
`w₀, w₀ + r, …, w₀ + (ℓ-1) r` with `r` in the Cantor set and `r ≠ 0`. -/
theorem vdW_infinite (C : CantorData) (L : ℕ) (hL : 1 ≤ L) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (χ : ℕ → Fin L) :
    ∃ w0 : ℕ, ∃ r : ℕ, C.Dig 0 r ∧ r ≠ 0 ∧ ∀ i < ℓ, χ (w0 + i * r) = χ w0 := by
  -- the closure of the forward orbit of `χ`
  set sh : (ℕ → Fin L) → (ℕ → Fin L) := fun η => leftShift η with hsh_def
  have hsh : Continuous sh := continuous_leftShift
  set O0 : Set (ℕ → Fin L) := range (fun m : ℕ => sh^[m] χ) with hO0
  have hinv : MapsTo sh (closure O0) (closure O0) := by
    intro z hz
    have h1 : sh '' O0 ⊆ O0 := by
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      exact ⟨m + 1, Function.iterate_succ_apply' sh m χ⟩
    exact closure_mono h1 (image_closure_subset_closure_image hsh ⟨z, hz, rfl⟩)
  -- the restriction of the shift to the orbit closure
  let X := ↥(closure O0)
  haveI : CompactSpace X := isCompact_iff_compactSpace.1 isClosed_closure.isCompact
  have hXne : Nonempty X := ⟨⟨χ, subset_closure ⟨0, rfl⟩⟩⟩
  let T' : X → X := fun z => ⟨sh z.1, hinv z.2⟩
  have hT' : Continuous T' := (hsh.comp continuous_subtype_val).subtype_mk _
  -- the cover by the colour of the zeroth coordinate
  let U : Fin L → Set X := fun c => {z | z.1 0 = c}
  have hev0 : Continuous fun z : X => z.1 0 :=
    (continuous_apply (A := fun _ : ℕ => Fin L) 0).comp continuous_subtype_val
  have hUo : ∀ c, IsOpen (U c) := fun c => hev0.isOpen_preimage ({c} : Set (Fin L)) (isOpen_discrete _)
  have hcov : ∀ z : X, ∃ c, z ∈ U c := fun z => ⟨z.1 0, rfl⟩
  haveI := hXne
  obtain ⟨c, x, r, hD, hr0, hprog⟩ :=
    CantorData.topological_vdW C hT' U hUo hcov ℓ hℓ 0
  -- the coordinates of the iterates of `x`
  have hxO : ∀ i ∈ Finset.range ℓ, x.1 (i * r) = c := by
    intro i hi
    have h1 := hprog i (Finset.mem_range.1 hi)
    have h2 : (T'^[i * r] x).1 0 = c := h1
    rw [CantorData.coe_iterate_restrict hinv (i * r) x] at h2
    have h3 := leftShift_iterate (i * r) x.1 0
    rw [zero_add] at h3
    rw [← h3]
    exact h2
  -- the open set of sequences with colour `c` at the positions `i r`
  let O : Set (ℕ → Fin L) := ⋂ i ∈ Finset.range ℓ, {η | η (i * r) = c}
  have hOo : IsOpen O := by
    refine isOpen_biInter_finset fun i _ => ?_
    exact (continuous_apply (A := fun _ : ℕ => Fin L) (i * r)).isOpen_preimage ({c} : Set (Fin L))
      (isOpen_discrete _)
  have hxO' : x.1 ∈ O := mem_iInter₂.2 fun i hi => hxO i hi
  obtain ⟨η, hηO, m, hm⟩ := mem_closure_iff.1 x.2 O hOo hxO'
  have hηm : η = sh^[m] χ := hm.symm
  subst hηm
  refine ⟨m, r, hD, hr0, fun i hi => ?_⟩
  have hcoord' : ∀ k : ℕ, (sh^[m] χ) k = χ (k + m) := fun k => leftShift_iterate m χ k
  have hi'' : (sh^[m] χ) (i * r) = c := mem_iInter₂.1 hηO i (Finset.mem_range.2 hi)
  have h0 : (sh^[m] χ) (0 * r) = c := mem_iInter₂.1 hηO 0 (Finset.mem_range.2 (by omega))
  rw [zero_mul, hcoord'] at h0
  rw [hcoord'] at hi''
  rw [zero_add] at h0
  rw [show m + i * r = i * r + m by ring]
  exact hi''.trans h0.symm

end CantorSzemeredi

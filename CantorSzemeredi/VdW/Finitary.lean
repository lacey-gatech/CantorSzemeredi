/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.VdW.Infinite

/-!
# The finitary van der Waerden theorem

Blueprint: `blueprint/src/chapter/vdw.tex`, `cor:vdw-finitary`.  For `L, ℓ ≥ 1` there is a bound `W`
such that every `L`-colouring of the window `[0, W]` contains a monochromatic `ℓ`-term progression
with common difference in `Cantor \ {0}` inside the window.  The proof is by contradiction, using
the sequential compactness of the colourings and the infinite case.
-/

namespace CantorSzemeredi

open Set Finset Filter Topology

/-- **Corollary `cor:vdw-finitary`.**  Finitary form: there is `W` such that every colouring of `ℕ`
with `L` colours has a monochromatic progression of length `ℓ` with common difference in the Cantor set
(not zero) lying in `[0, W]`. -/
theorem vdW_finitary (C : CantorData) (L ℓ : ℕ) (hL : 1 ≤ L) (hℓ : 1 ≤ ℓ) :
    ∃ W : ℕ, ∀ χ : ℕ → Fin L, ∃ w0 r : ℕ, C.Dig 0 r ∧ r ≠ 0 ∧ w0 + (ℓ - 1) * r ≤ W ∧
      ∀ i < ℓ, χ (w0 + i * r) = χ w0 := by
  by_contra hcon
  push_neg at hcon
  choose χs hχs using hcon
  -- the colourings `χs W` form a sequence in the compact space `(ℕ → Fin L)`
  obtain ⟨χ, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq
    (x := fun W : ℕ => χs W) (fun W => mem_univ _)
  obtain ⟨w0, r, hD, hr0, hmono⟩ := vdW_infinite C L hL ℓ hℓ χ
  set W0 : ℕ := w0 + (ℓ - 1) * r with hW0
  -- the colourings agree with `χ` on `[0, W0]` for late enough terms of the subsequence
  have hagree : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (W0 + 1), χs (φ n) k = χ k := by
    refine (Finset.range (W0 + 1)).eventually_all.2 fun k _ => ?_
    have hk := (tendsto_pi_nhds.1 hlim k)
    exact hk.eventually (isOpen_discrete {χ k} |>.mem_nhds rfl)
  obtain ⟨n, hn⟩ := (hagree.and (eventually_ge_atTop W0)).exists
  obtain ⟨hagree_n, hW⟩ := hn
  have hφn : W0 ≤ φ n := le_trans hW (StrictMono.id_le hφ n)
  -- the colouring `χs (φ n)` inherits the progression: a contradiction
  obtain ⟨i, hi, hne⟩ := hχs (φ n) w0 r hD hr0 (by omega)
  apply hne
  have hval : ∀ j ≤ W0, χs (φ n) j = χ j := fun j hj => hagree_n j (Finset.mem_range.2 (by omega))
  have hir : i * r ≤ (ℓ - 1) * r := Nat.mul_le_mul_right r (by omega)
  have hj1 : w0 + i * r ≤ W0 := by omega
  have hj0 : w0 ≤ W0 := by omega
  rw [hval _ hj1, hval _ hj0]
  exact hmono i hi

end CantorSzemeredi

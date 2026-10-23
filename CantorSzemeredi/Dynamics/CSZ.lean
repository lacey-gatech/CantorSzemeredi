/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.System
import CantorSzemeredi.Cantor.Enum

/-!
# The Cantor–Szemerédi property

Blueprint: `blueprint/src/chapter/csz.tex`, Definition `def:csz`.

A system is *CSZ* if for every measurable `A` of positive measure, every `t ≥ 1`, every
dilation `i ≥ 0`, and **every** Cantor set `C_{b,D}` with `0 ∈ D`,

  `liminf_{N-M → ∞}  E_{M ≤ n < N}  m (A ∩ T^{-b^i k_n} A ∩ ⋯ ∩ T^{-t b^i k_n} A)  >  0`,

the `liminf` being over all windows of indices of growing length — the *uniform* `liminf` of
`CantorSzemeredi.uniformLiminf`.

Two warnings from the blueprint, both of which the Lean statement is designed to respect.

* The quantifier over Cantor sets is inside, and the dilation `i` is a power of **that** set's
  base `b`.  So CSZ for `(X, 𝒜, m, T)` does *not* give CSZ for `(X, 𝒜, m, T^(b^i))`; only the
  single instance at a fixed Cantor set is available (`rem:dilation`).
* The averages are uniform in the window, which is what converts positivity into a syndetic
  set of good indices, via `syndetic_of_uniformLiminf_pos`.
-/

namespace CantorSzemeredi

open MeasureTheory

namespace MPS

variable (S : MPS)

/-- The multiple correlation `m (A ∩ T^{-d} A ∩ ⋯ ∩ T^{-t d} A)`, as a real number.

This is `∫ ∏_{s=0}^{t} T^{s d} 1_A dm`; writing it as a measure of an intersection avoids
carrying integrals of products of indicators through the whole development. -/
noncomputable def multiCorr (A : Set S.X) (t d : ℕ) : ℝ :=
  (S.m (⋂ s ∈ Finset.range (t + 1), (S.T^[s * d]) ⁻¹' A)).toReal

theorem multiCorr_nonneg (A : Set S.X) (t d : ℕ) : 0 ≤ S.multiCorr A t d :=
  ENNReal.toReal_nonneg

/-- `multiCorr` at `d = 0` is just `m A`: every factor is `A` itself. -/
theorem multiCorr_zero (A : Set S.X) (t : ℕ) : S.multiCorr A t 0 = (S.m A).toReal := by
  have : (⋂ s ∈ Finset.range (t + 1), (S.T^[s * 0]) ⁻¹' A) = A := by
    ext x
    simp only [Set.mem_iInter, Finset.mem_range, Nat.mul_zero, Function.iterate_zero,
      Set.preimage_id, id_eq]
    exact ⟨fun h => h 0 (Nat.succ_pos t), fun h _ _ => h⟩
  rw [multiCorr, this]

end MPS

namespace MPS

namespace Factor

variable {S : MPS}

/-- **Definition `def:csz`.**  The factor `D` is *Cantor–Szemerédi*.

Note the order of quantifiers: the Cantor set `C` is quantified inside, so the dilations
available at `C` are powers of `C`'s own base. -/
def CSZ (D : Factor S) : Prop :=
  ∀ (C : CantorData) (A : Set S.X), MeasurableSet[D.σ] A → 0 < S.m A →
    ∀ t : ℕ, 1 ≤ t → ∀ i : ℕ,
      0 < uniformLiminf fun n => S.multiCorr A t (C.base ^ i * C.enum n)

/-- If `A` is conull then every multiple correlation is `1`. -/
theorem multiCorr_of_univ {S : MPS} {A : Set S.X} (hA : A = Set.univ) (t d : ℕ) :
    S.multiCorr A t d = 1 := by
  subst hA
  simp [MPS.multiCorr]

/-- **Lemma `lem:trivial-csz`.**  The trivial factor is CSZ.

If `A` is in the trivial factor and has positive measure then `A` is conull, so every
correlation is `1` and the uniform average is identically `1`. -/
theorem trivial_CSZ (S : MPS) : (Factor.trivial S).CSZ := by
  intro C A hA hpos t _ i
  -- `A` is `⊥`-measurable and not null, hence `Set.univ`.
  have huniv : A = Set.univ := by
    rcases MeasurableSpace.measurableSet_bot_iff.1 hA with rfl | h
    · simp at hpos
    · exact h
  have hone : ∀ n : ℕ, S.multiCorr A t (C.base ^ i * C.enum n) = 1 :=
    fun n => multiCorr_of_univ huniv _ _
  -- The averages are identically `1` on every non-degenerate window.
  have havg : ∀ᶠ p in uniformFilter,
      uniformAvg (fun n => S.multiCorr A t (C.base ^ i * C.enum n)) p.1 p.2 = 1 := by
    rw [Filter.eventually_iff, mem_uniformFilter_iff]
    refine ⟨1, fun M N hMN => ?_⟩
    have hlt : M < N := by omega
    simp only [Set.mem_setOf_eq, uniformAvg]
    rw [Finset.sum_congr rfl fun n _ => hone n]
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    exact div_self (by
      have : 0 < N - M := by omega
      exact_mod_cast Nat.cast_ne_zero.2 this.ne')
  have : uniformLiminf (fun n => S.multiCorr A t (C.base ^ i * C.enum n)) = 1 := by
    rw [uniformLiminf]
    exact Filter.liminf_congr havg ▸ Filter.liminf_const 1
  rw [this]
  norm_num

end Factor

end MPS

end CantorSzemeredi

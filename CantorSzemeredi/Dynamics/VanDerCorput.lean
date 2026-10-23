/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Basic

/-!
# The van der Corput inequality

Blueprint: `lem:vdc` in `blueprint/src/chapter/mps.tex`.  This is the starting point of the
weakly mixing chapter: it converts an average of vectors into an average of their correlations
at the shifts `1 ≤ h ≤ H`.

## Indexing

Indices run over `ℤ`, not `ℕ`.  The proof sums over the window `m ∈ [M-H, N)`, and with `ℕ`
subtraction `M - H` truncates at `0` when `M < H`, which breaks the covering argument that
each `w n` is hit exactly `H` times.  Over `ℤ` there is no such trap.

The vectors lie in a **real** inner product space: everything downstream (`condInner`, `L²` of
real functions) is real, and this makes the symmetry `S(-r) = S(r)` immediate rather than a
statement about complex conjugates.
-/

namespace CantorSzemeredi

open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Translating the window of a sum over `ℤ`. -/
theorem sum_Ico_translate {M' : Type*} [AddCommMonoid M'] (f : ℤ → M') (a b t : ℤ) :
    ∑ n ∈ Finset.Ico a b, f n = ∑ m ∈ Finset.Ico (a - t) (b - t), f (m + t) := by
  have hmap : (Finset.Ico (a - t) (b - t)).map (addRightEmbedding t) = Finset.Ico a b := by
    rw [Finset.map_add_right_Ico]
    congr 1 <;> ring
  rw [← hmap, Finset.sum_map]
  rfl

/-- `corr w M N r = ∑_{n ∈ [M,N)} ⟨w (n+r), w n⟩`, the correlation of `w` with its shift. -/
noncomputable def corr (w : ℤ → E) (M N : ℤ) (r : ℤ) : ℝ :=
  ∑ n ∈ Finset.Ico M N, inner ℝ (w (n + r)) (w n)

/-- The hypotheses of the van der Corput inequality: `w` is supported in the window `[M, N)`
and bounded by `1`. -/
structure VdCData (w : ℤ → E) (M N : ℤ) : Prop where
  /-- `w` is bounded by `1`. -/
  norm_le : ∀ n, ‖w n‖ ≤ 1
  /-- `w` vanishes off the window. -/
  zero_of_notMem : ∀ n, n ∉ Finset.Ico M N → w n = 0

namespace VdCData

variable {w : ℤ → E} {M N : ℤ}

/-- A sum of `w` over any interval containing the window equals the sum over the window. -/
theorem sum_Ico_eq (hw : VdCData w M N) {a b : ℤ} (ha : a ≤ M) (hb : N ≤ b) :
    ∑ n ∈ Finset.Ico a b, w n = ∑ n ∈ Finset.Ico M N, w n := by
  rw [← Finset.sum_subset (Finset.Ico_subset_Ico ha hb)]
  intro n _ hn
  exact hw.zero_of_notMem n hn

/-- Translating the window of summation. -/
theorem sum_Ico_shift (hw : VdCData w M N) {a b : ℤ} (h : ℤ) (ha : a + h ≤ M) (hb : N ≤ b + h) :
    ∑ m ∈ Finset.Ico a b, w (m + h) = ∑ n ∈ Finset.Ico M N, w n := by
  have hset : Finset.Ico (a + h - h) (b + h - h) = Finset.Ico a b := by
    congr 1 <;> omega
  have hrw : ∑ m ∈ Finset.Ico a b, w (m + h) = ∑ n ∈ Finset.Ico (a + h) (b + h), w n := by
    rw [sum_Ico_translate w (a + h) (b + h) h, hset]
  rw [hrw]
  exact hw.sum_Ico_eq (by omega) (by omega)

/-- **Step (A): the covering identity.**  Summing `∑_{h=1}^{H} w (m+h)` over `m ∈ [M-H, N)`
counts every `w n`, `n ∈ [M, N)`, exactly `H` times. -/
theorem sum_sum_shift (hw : VdCData w M N) {H : ℤ} (hH : 1 ≤ H) :
    ∑ m ∈ Finset.Ico (M - H) N, ∑ h ∈ Finset.Icc 1 H, w (m + h)
      = H.toNat • ∑ n ∈ Finset.Ico M N, w n := by
  rw [Finset.sum_comm]
  have hterm : ∀ h ∈ Finset.Icc (1 : ℤ) H,
      ∑ m ∈ Finset.Ico (M - H) N, w (m + h) = ∑ n ∈ Finset.Ico M N, w n := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    exact hw.sum_Ico_shift h (by omega) (by omega)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Int.card_Icc]
  congr 2
  omega

/-- The correlation sum may be taken over any interval containing the window. -/
theorem corr_eq_sum_Ico (hw : VdCData w M N) (r : ℤ) {a b : ℤ} (ha : a ≤ M) (hb : N ≤ b) :
    ∑ n ∈ Finset.Ico a b, (inner ℝ (w (n + r)) (w n) : ℝ) = corr w M N r := by
  rw [corr, ← Finset.sum_subset (Finset.Ico_subset_Ico ha hb)]
  intro n _ hn
  rw [hw.zero_of_notMem n hn, inner_zero_right]

/-- The correlation sum is symmetric in `±r`, the inner product being real. -/
theorem corr_neg (hw : VdCData w M N) (r : ℤ) : corr w M N (-r) = corr w M N r := by
  have habs : 0 ≤ |r| := abs_nonneg r
  have hr₁ : -|r| ≤ r := neg_abs_le r
  have hr₂ : r ≤ |r| := le_abs_self r
  rw [← hw.corr_eq_sum_Ico (-r) (a := M - |r|) (b := N + |r|) (by omega) (by omega),
    ← hw.corr_eq_sum_Ico r (a := M - |r| - r) (b := N + |r| - r) (by omega) (by omega),
    sum_Ico_translate (fun n => (inner ℝ (w (n + -r)) (w n) : ℝ)) (M - |r|) (N + |r|) r]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show m + r + -r = m by ring]
  exact real_inner_comm _ _

end VdCData

end CantorSzemeredi

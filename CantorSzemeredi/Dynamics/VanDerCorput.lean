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

/-- Casting `Int.toNat` through to `ℝ`. -/
theorem cast_toNat {x : ℤ} (hx : 0 ≤ x) : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hx]

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

omit [InnerProductSpace ℝ E] in
/-- A sum of `w` over any interval containing the window equals the sum over the window. -/
theorem sum_Ico_eq (hw : VdCData w M N) {a b : ℤ} (ha : a ≤ M) (hb : N ≤ b) :
    ∑ n ∈ Finset.Ico a b, w n = ∑ n ∈ Finset.Ico M N, w n := by
  rw [← Finset.sum_subset (Finset.Ico_subset_Ico ha hb)]
  intro n _ hn
  exact hw.zero_of_notMem n hn

omit [InnerProductSpace ℝ E] in
/-- Translating the window of summation. -/
theorem sum_Ico_shift (hw : VdCData w M N) {a b : ℤ} (h : ℤ) (ha : a + h ≤ M) (hb : N ≤ b + h) :
    ∑ m ∈ Finset.Ico a b, w (m + h) = ∑ n ∈ Finset.Ico M N, w n := by
  have hset : Finset.Ico (a + h - h) (b + h - h) = Finset.Ico a b := by
    congr 1 <;> omega
  have hrw : ∑ m ∈ Finset.Ico a b, w (m + h) = ∑ n ∈ Finset.Ico (a + h) (b + h), w n := by
    rw [sum_Ico_translate w (a + h) (b + h) h, hset]
  rw [hrw]
  exact hw.sum_Ico_eq (by omega) (by omega)

omit [InnerProductSpace ℝ E] in
/-- **Step (A): the covering identity.**  Summing `∑_{h=1}^{H} w (m+h)` over `m ∈ [M-H, N)`
counts every `w n`, `n ∈ [M, N)`, exactly `H` times. -/
theorem sum_sum_shift (hw : VdCData w M N) {H : ℤ} (_hH : 1 ≤ H) :
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

/-- **Step (C): each double shift is a correlation.**  Summing `⟨w (m+h), w (m+h')⟩` over the
window gives exactly `corr w M N (h - h')`. -/
theorem sum_inner_shift (hw : VdCData w M N) {H h h' : ℤ}
    (hh' : h' ∈ Finset.Icc 1 H) :
    ∑ m ∈ Finset.Ico (M - H) N, (inner ℝ (w (m + h)) (w (m + h')) : ℝ)
      = corr w M N (h - h') := by
  rw [Finset.mem_Icc] at hh'
  have hset : Finset.Ico (M - H + h' - h') (N + h' - h') = Finset.Ico (M - H) N := by
    congr 1 <;> omega
  rw [← hw.corr_eq_sum_Ico (h - h') (a := M - H + h') (b := N + h') (by omega) (by omega),
    sum_Ico_translate (fun n => (inner ℝ (w (n + (h - h'))) (w n) : ℝ)) (M - H + h') (N + h') h',
    hset]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show m + h' + (h - h') = m + h by ring]

/-- **Steps (B) and (C) combined.**  Cauchy–Schwarz over the window, then expansion of each
`‖∑_h w (m+h)‖²` into correlations:

  `H² ‖∑_{n ∈ [M,N)} w n‖²  ≤  (N - M + H) * ∑_{h, h' ∈ [1,H]} corr w M N (h - h')`. -/
theorem sq_norm_sum_le (hw : VdCData w M N) {H : ℤ} (hH : 1 ≤ H) :
    ((H : ℝ) * ‖∑ n ∈ Finset.Ico M N, w n‖) ^ 2
      ≤ ((N - (M - H)).toNat : ℝ)
          * ∑ h ∈ Finset.Icc 1 H, ∑ h' ∈ Finset.Icc 1 H, corr w M N (h - h') := by
  set I := Finset.Ico (M - H) N with hI
  set v : ℤ → E := fun m => ∑ h ∈ Finset.Icc 1 H, w (m + h) with hv
  -- The covering identity turns the left side into a sum over the window `I`.
  have hcov : ∑ m ∈ I, v m = H.toNat • ∑ n ∈ Finset.Ico M N, w n := hw.sum_sum_shift hH
  have hHtoNat : ((H.toNat : ℤ) : ℝ) = (H : ℝ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  have hleft : (H : ℝ) * ‖∑ n ∈ Finset.Ico M N, w n‖ = ‖∑ m ∈ I, v m‖ := by
    rw [hcov, show (H.toNat • ∑ n ∈ Finset.Ico M N, w n)
        = (H.toNat : ℝ) • ∑ n ∈ Finset.Ico M N, w n by
      rw [Nat.cast_smul_eq_nsmul], norm_smul]
    simp only [Real.norm_natCast]
    congr 1
    rw [← hHtoNat]
    norm_cast
  rw [hleft]
  -- Cauchy–Schwarz over `m ∈ I`.
  have hcs : ‖∑ m ∈ I, v m‖ ^ 2 ≤ (I.card : ℝ) * ∑ m ∈ I, ‖v m‖ ^ 2 := by
    calc ‖∑ m ∈ I, v m‖ ^ 2 ≤ (∑ m ∈ I, ‖v m‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (I.card : ℝ) * ∑ m ∈ I, ‖v m‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  refine hcs.trans ?_
  -- Expand each `‖v m‖²` and exchange the order of summation.
  have hexp : ∀ m, ‖v m‖ ^ 2
      = ∑ h ∈ Finset.Icc 1 H, ∑ h' ∈ Finset.Icc 1 H, (inner ℝ (w (m + h)) (w (m + h')) : ℝ) := by
    intro m
    rw [← real_inner_self_eq_norm_sq, hv]
    rw [sum_inner]
    exact Finset.sum_congr rfl fun h _ => inner_sum _ _ _
  have hswap : ∑ m ∈ I, ‖v m‖ ^ 2
      = ∑ h ∈ Finset.Icc 1 H, ∑ h' ∈ Finset.Icc 1 H, corr w M N (h - h') := by
    rw [Finset.sum_congr rfl fun m _ => hexp m]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun h' hh' => hw.sum_inner_shift hh'
  rw [hswap, hI, Int.card_Ico]

/-! ### Counting the pairs `(h, h')`

For fixed `h`, the map `h' ↦ h - h'` is injective, so the shifts `r = h - h'` occurring are
distinct and lie in `[1-H, H-1]`.  Folding `±r` together with `corr_neg` turns the inner sum
into `|corr 0| + 2 ∑_{r=1}^{H-1} |corr r|`. -/

/-- The symmetric interval splits into `0`, the positives, and the negatives. -/
theorem Icc_symm_eq (H : ℤ) (hH : 1 ≤ H) :
    Finset.Icc (1 - H) (H - 1)
      = ((Finset.Icc 1 (H - 1)).image (fun r => -r)) ∪ Finset.Icc 0 (H - 1) := by
  ext r
  simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_image]
  constructor
  · intro h
    rcases le_or_gt 0 r with hr | hr
    · exact Or.inr ⟨hr, h.2⟩
    · exact Or.inl ⟨-r, ⟨by omega, by omega⟩, by ring⟩
  · rintro (⟨q, ⟨hq₁, hq₂⟩, rfl⟩ | ⟨h₁, h₂⟩) <;> omega

/-- Folding `±r`: a symmetric non-negative function summed over `[1-H, H-1]`. -/
theorem sum_Icc_symm {g : ℤ → ℝ} (hg : ∀ r, g (-r) = g r) (H : ℤ) (hH : 1 ≤ H) :
    ∑ r ∈ Finset.Icc (1 - H) (H - 1), g r
      = g 0 + 2 * ∑ r ∈ Finset.Icc 1 (H - 1), g r := by
  rw [Icc_symm_eq H hH, Finset.sum_union, Finset.sum_image]
  · have hzero : Finset.Icc (0 : ℤ) (H - 1) = insert 0 (Finset.Icc 1 (H - 1)) := by
      ext r
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hzero, Finset.sum_insert (by simp)]
    rw [Finset.sum_congr rfl fun r _ => hg r]
    ring
  · intro a _ b _ hab
    simpa using hab
  · rw [Finset.disjoint_left]
    rintro r hr hr'
    simp only [Finset.mem_image, Finset.mem_Icc] at hr hr'
    obtain ⟨q, ⟨hq₁, hq₂⟩, rfl⟩ := hr
    omega

/-- For fixed `h`, the inner sum over `h'` is bounded by the symmetric sum over all shifts. -/
theorem sum_corr_row_le (hw : VdCData w M N) {H h : ℤ} (hH : 1 ≤ H)
    (hh : h ∈ Finset.Icc 1 H) :
    ∑ h' ∈ Finset.Icc 1 H, corr w M N (h - h')
      ≤ |corr w M N 0| + 2 * ∑ r ∈ Finset.Icc 1 (H - 1), |corr w M N r| := by
  rw [Finset.mem_Icc] at hh
  -- Bound each term by its absolute value, then reindex `h' ↦ r = h - h'`.
  have hle : ∑ h' ∈ Finset.Icc 1 H, corr w M N (h - h')
      ≤ ∑ h' ∈ Finset.Icc 1 H, |corr w M N (h - h')| :=
    Finset.sum_le_sum fun h' _ => le_abs_self _
  refine hle.trans ?_
  -- The reindexed sum sits inside the symmetric interval.
  have hreindex : ∑ h' ∈ Finset.Icc 1 H, |corr w M N (h - h')|
      = ∑ r ∈ Finset.Icc (h - H) (h - 1), |corr w M N r| := by
    refine Finset.sum_nbij' (i := fun h' => h - h') (j := fun r => h - r) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb ⊢
      omega
    · intro a _
      ring
    · intro b _
      ring
    · intro a _
      rfl
  rw [hreindex]
  have hsubset : Finset.Icc (h - H) (h - 1) ⊆ Finset.Icc (1 - H) (H - 1) := by
    refine Finset.Icc_subset_Icc (by omega) (by omega)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun r _ _ => abs_nonneg _)) ?_
  rw [sum_Icc_symm (fun r => (hw.corr_neg r) ▸ rfl) H hH]

/-- `corr w M N 0 = ∑ ‖w n‖²`, which is at most the length of the window. -/
theorem corr_zero_le (hw : VdCData w M N) (hMN : M ≤ N) :
    |corr w M N 0| ≤ ((N - M : ℤ) : ℝ) := by
  have hnn : 0 ≤ corr w M N 0 := by
    refine Finset.sum_nonneg fun n _ => ?_
    rw [show n + (0 : ℤ) = n by ring]
    exact real_inner_self_nonneg
  rw [abs_of_nonneg hnn, corr]
  have hterm : ∀ n ∈ Finset.Ico M N, (inner ℝ (w (n + 0)) (w n) : ℝ) ≤ 1 := by
    intro n _
    rw [show n + (0 : ℤ) = n by ring, real_inner_self_eq_norm_sq]
    have := hw.norm_le n
    nlinarith [norm_nonneg (w n)]
  calc ∑ n ∈ Finset.Ico M N, (inner ℝ (w (n + 0)) (w n) : ℝ)
      ≤ ∑ _n ∈ Finset.Ico M N, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = ((N - M : ℤ) : ℝ) := by
        rw [Finset.sum_const, Int.card_Ico, nsmul_eq_mul, mul_one,
          cast_toNat (by omega)]

/-- **The van der Corput inequality (`lem:vdc`).**

  `‖E_{M ≤ n < N} w n‖² ≤ 4 E_{1 ≤ h ≤ H} (|corr w M N h| / (N-M)) + 2/H`.

This is slightly stronger than the form in the blueprint, which has
`|E_{M ≤ n < N-h} ⟨w(n+h), w n⟩|` on the right: that average divides by `N - M - h`, whereas
`corr` divides by the larger `N - M`, so the bound here implies the blueprint's. -/
theorem van_der_corput (hw : VdCData w M N) {H : ℤ} (hH : 1 ≤ H) (hHL : H < N - M) :
    ‖(((N - M : ℤ) : ℝ))⁻¹ • ∑ n ∈ Finset.Ico M N, w n‖ ^ 2
      ≤ 4 * ((H : ℝ)⁻¹ * ∑ h ∈ Finset.Icc 1 H, |corr w M N h| / ((N - M : ℤ) : ℝ))
          + 2 / (H : ℝ) := by
  set L : ℝ := ((N - M : ℤ) : ℝ) with hLdef
  have hLZ : (0 : ℤ) < N - M := by omega
  have hLR : (0 : ℝ) < L := by rw [hLdef]; exact_mod_cast hLZ
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hHLR : (H : ℝ) ≤ L := by rw [hLdef]; exact_mod_cast hHL.le
  set S : ℝ := ∑ r ∈ Finset.Icc 1 (H - 1), |corr w M N r| with hS
  set S' : ℝ := ∑ h ∈ Finset.Icc 1 H, |corr w M N h| with hS'
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hSS' : S ≤ S' := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (by omega))
      fun _ _ _ => abs_nonneg _
  -- The double sum of correlations.
  have hdouble : ∑ h ∈ Finset.Icc 1 H, ∑ h' ∈ Finset.Icc 1 H, corr w M N (h - h')
      ≤ (H : ℝ) * (L + 2 * S) := by
    refine le_trans (Finset.sum_le_sum fun h hh => hw.sum_corr_row_le hH hh) ?_
    rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul, show H + 1 - 1 = H by ring,
      cast_toNat (show (0:ℤ) ≤ H by omega)]
    have := hw.corr_zero_le (by omega)
    nlinarith [hSnn]
  -- Cauchy–Schwarz plus expansion.
  have hcard : (((N - (M - H)).toNat : ℕ) : ℝ) = L + (H : ℝ) := by
    rw [cast_toNat (by omega), hLdef]
    push_cast
    ring
  have hmain := hw.sq_norm_sum_le hH
  rw [hcard] at hmain
  have hsq : ((H : ℝ) * ‖∑ n ∈ Finset.Ico M N, w n‖) ^ 2 ≤ (L + H) * ((H : ℝ) * (L + 2 * S)) := by
    refine hmain.trans ?_
    exact mul_le_mul_of_nonneg_left hdouble (by positivity)
  -- Divide through.
  have hnorm : ‖(L)⁻¹ • ∑ n ∈ Finset.Ico M N, w n‖ ^ 2
      = (L)⁻¹ ^ 2 * ‖∑ n ∈ Finset.Ico M N, w n‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow]
  have hsum_div : ∑ h ∈ Finset.Icc 1 H, |corr w M N h| / L = S' / L := by
    rw [hS', Finset.sum_div]
  rw [hnorm, hsum_div]
  -- `‖∑ w‖² ≤ (L+H)(L+2S)/H`.
  have hX : ‖∑ n ∈ Finset.Ico M N, w n‖ ^ 2 ≤ (L + H) * (L + 2 * S) / (H : ℝ) := by
    rw [le_div_iff₀ hHR]
    nlinarith [hsq]
  -- The elementary inequality behind the constants `4` and `2`.
  have hkey : (L + (H : ℝ)) * (L + 2 * S) ≤ 4 * L * S' + 2 * L ^ 2 := by
    nlinarith [hSS', hSnn, hHLR, hLR]
  have hstep : (L)⁻¹ ^ 2 * ((L + H) * (L + 2 * S) / (H : ℝ))
      ≤ (L)⁻¹ ^ 2 * ((4 * L * S' + 2 * L ^ 2) / (H : ℝ)) := by
    have : (0 : ℝ) ≤ (L)⁻¹ ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_left (by gcongr) this
  have hfinal : (L)⁻¹ ^ 2 * ((4 * L * S' + 2 * L ^ 2) / (H : ℝ))
      = 4 * ((H : ℝ)⁻¹ * (S' / L)) + 2 / (H : ℝ) := by
    field_simp
  calc (L)⁻¹ ^ 2 * ‖∑ n ∈ Finset.Ico M N, w n‖ ^ 2
      ≤ (L)⁻¹ ^ 2 * ((L + H) * (L + 2 * S) / (H : ℝ)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ ≤ (L)⁻¹ ^ 2 * ((4 * L * S' + 2 * L ^ 2) / (H : ℝ)) := hstep
    _ = 4 * ((H : ℝ)⁻¹ * (S' / L)) + 2 / (H : ℝ) := hfinal

/-- **The van der Corput inequality in the blueprint's form.**

  `‖E_{M ≤ n < N} w n‖² ≤ 4 E_{1 ≤ h ≤ H} |E_{M ≤ n < N-h} ⟨w(n+h), w n⟩| + 2/H`,

obtained from `van_der_corput` by noting that `corr w M N h` is a sum over `[M, N-h)` (the
terms with `n + h ≥ N` vanish), so dividing it by `N - M` rather than by `N - M - h` only
decreases it. -/
theorem van_der_corput_avg (hw : VdCData w M N) {H : ℤ} (hH : 1 ≤ H) (hHL : H < N - M) :
    ‖(((N - M : ℤ) : ℝ))⁻¹ • ∑ n ∈ Finset.Ico M N, w n‖ ^ 2
      ≤ 4 * ((H : ℝ)⁻¹ * ∑ h ∈ Finset.Icc 1 H,
          |corr w M N h| / ((N - M - h : ℤ) : ℝ)) + 2 / (H : ℝ) := by
  refine (hw.van_der_corput hH hHL).trans ?_
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hmono : ∑ h ∈ Finset.Icc 1 H, |corr w M N h| / ((N - M : ℤ) : ℝ)
      ≤ ∑ h ∈ Finset.Icc 1 H, |corr w M N h| / ((N - M - h : ℤ) : ℝ) := by
    refine Finset.sum_le_sum fun h hh => ?_
    rw [Finset.mem_Icc] at hh
    have h₁ : (0 : ℝ) < ((N - M - h : ℤ) : ℝ) := by
      have : (0 : ℤ) < N - M - h := by omega
      exact_mod_cast this
    have h₂ : ((N - M - h : ℤ) : ℝ) ≤ ((N - M : ℤ) : ℝ) := by
      have : (N - M - h : ℤ) ≤ (N - M : ℤ) := by omega
      exact_mod_cast this
    gcongr
  have hscaled : (H : ℝ)⁻¹ * ∑ h ∈ Finset.Icc 1 H, |corr w M N h| / ((N - M : ℤ) : ℝ)
      ≤ (H : ℝ)⁻¹ * ∑ h ∈ Finset.Icc 1 H, |corr w M N h| / ((N - M - h : ℤ) : ℝ) :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  linarith

end VdCData

end CantorSzemeredi

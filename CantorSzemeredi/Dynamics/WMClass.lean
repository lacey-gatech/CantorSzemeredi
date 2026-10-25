/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMShift

/-!
# Averages over a residue class, as averages over blocks

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`, Step 1, "Undoing the
re-indexing".  For `q = δ^ℓ` and a residue `c < q`, the indices `n ∈ [M,N)` with `n ≡ c mod q`
are exactly `n = q a + c` with `a` in the block window `[A(M), A(N))`, where
`A(M) = ⌈(M - c)/q⌉`.  So an average over the residue class is an average over the block
window, with the same count, and the window length is comparable to `(N - M)/q`.
-/

namespace CantorSzemeredi

open Finset Filter Topology MeasureTheory

/-- The first block index `a` with `q a + c ≥ M`, namely `⌈(M - c)/q⌉`. -/
def blockStart (q c M : ℕ) : ℕ := (M + (q - 1 - c)) / q

/-- `A(M) ≤ a` exactly when `M ≤ q a + c`. -/
theorem blockStart_le_iff {q c : ℕ} (hq : 0 < q) (hc : c < q) (a M : ℕ) :
    blockStart q c M ≤ a ↔ M ≤ q * a + c := by
  unfold blockStart
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hq, Nat.succ_mul, mul_comm]
  have h1 : q - 1 - c + c + 1 = q := by omega
  generalize q * a = r
  omega

/-- The residue class of `c` in `[M,N)` is the block window, reindexed by `a ↦ q a + c`. -/
theorem sum_class_eq {q c : ℕ} (hq : 0 < q) (hc : c < q) (f : ℕ → ℝ) (M N : ℕ) :
    ∑ n ∈ (Ico M N).filter (fun n => n % q = c), f n
      = ∑ a ∈ Ico (blockStart q c M) (blockStart q c N), f (q * a + c) := by
  symm
  refine Finset.sum_nbij' (fun a => q * a + c) (fun n => n / q) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Ico] at ha
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (blockStart_le_iff hq hc a M).1 ha.1
    · by_contra hcon
      have := (blockStart_le_iff hq hc a N).2 (by omega)
      omega
    · rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hc]
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Ico] at hn
    rw [Finset.mem_Ico]
    have hA : blockStart q c M ≤ n / q := by
      rw [blockStart_le_iff hq hc]
      have := Nat.div_add_mod n q
      rw [hn.2] at this
      omega
    refine ⟨hA, ?_⟩
    have hB : ¬ (blockStart q c N ≤ n / q) := by
      rw [blockStart_le_iff hq hc, not_le]
      have := Nat.div_add_mod n q
      rw [hn.2] at this
      omega
    omega
  · intro a _
    rw [Nat.mul_add_div hq, Nat.div_eq_of_lt hc, add_zero]
  · intro n hn
    rw [Finset.mem_filter] at hn
    have := Nat.div_add_mod n q
    rw [hn.2] at this
    exact this
  · intro a _
    rfl

/-- The block window is monotone in `M`. -/
theorem blockStart_mono {q c : ℕ} (hq : 0 < q) {M N : ℕ} (h : M ≤ N) :
    blockStart q c M ≤ blockStart q c N :=
  Nat.div_le_div_right (by omega)

/-- The block window has length at least `(N - M)/q` up to an error of `2`: `N` lies below
`M + (A(N) - A(M)) q + 2q`. -/
theorem lt_blockStart_length {q c : ℕ} (hq : 0 < q) (hc : c < q) (M N : ℕ) (hMN : M ≤ N) :
    N < M + (blockStart q c N - blockStart q c M) * q + 2 * q := by
  have hmono := blockStart_mono (c := c) hq hMN
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, blockStart q c N = blockStart q c M + Δ :=
    ⟨_, (Nat.add_sub_cancel' hmono).symm⟩
  rw [hΔ, Nat.add_sub_cancel_left]
  have hN : N < blockStart q c N * q + q := by
    have h1 : (N + (q - 1 - c)) / q * q + (N + (q - 1 - c)) % q = N + (q - 1 - c) := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have h2 := Nat.mod_lt (N + (q - 1 - c)) hq
    unfold blockStart
    omega
  have hM : blockStart q c M * q ≤ M + q := by
    have h1 : (M + (q - 1 - c)) / q * q + (M + (q - 1 - c)) % q = M + (q - 1 - c) := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have h2 := Nat.mod_lt (M + (q - 1 - c)) hq
    unfold blockStart
    omega
  rw [hΔ] at hN
  nlinarith

/-- The window map `(M,N) ↦ (A(M), A(N))` sends the uniform filter to itself. -/
theorem tendsto_blockStart {q c : ℕ} (hq : 0 < q) (hc : c < q) :
    Tendsto (fun p : ℕ × ℕ => (blockStart q c p.1, blockStart q c p.2)) uniformFilter
      uniformFilter := by
  unfold uniformFilter
  refine tendsto_iInf.2 fun L => tendsto_principal.2 ?_
  have hS : {p : ℕ × ℕ | (L + 1) * q ≤ p.2 - p.1} ∈
      ⨅ L' : ℕ, 𝓟 {p : ℕ × ℕ | L' ≤ p.2 - p.1} :=
    Filter.le_principal_iff.1 (iInf_le (fun L' : ℕ => 𝓟 {p : ℕ × ℕ | L' ≤ p.2 - p.1}) ((L + 1) * q))
  refine Filter.eventually_of_mem hS fun p hp => ?_
  have hp' : (L + 1) * q ≤ p.2 - p.1 := hp
  have hpos : 0 < (L + 1) * q := by positivity
  have hMN : p.1 ≤ p.2 := by
    by_contra h
    have : p.2 - p.1 = 0 := by omega
    omega
  show L ≤ blockStart q c p.2 - blockStart q c p.1
  by_contra hcon
  have hlen := lt_blockStart_length hq hc p.1 p.2 hMN
  have h3 : (blockStart q c p.2 - blockStart q c p.1 + 1) * q ≤ L * q :=
    Nat.mul_le_mul_right q (by omega)
  have h4 : (L + 1) * q = L * q + q := by ring
  have h5 : (blockStart q c p.2 - blockStart q c p.1 + 1) * q
      = (blockStart q c p.2 - blockStart q c p.1) * q + q := by ring
  omega

/-- The residue class has as many elements as the block window. -/
theorem card_class_eq {q c : ℕ} (hq : 0 < q) (hc : c < q) (M N : ℕ) :
    ((Ico M N).filter (fun n => n % q = c)).card = blockStart q c N - blockStart q c M := by
  have h := sum_class_eq (f := fun _ => (1 : ℝ)) hq hc M N
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico] at h
  exact_mod_cast h

/-- The class average over `n` equals the block average over `a`, pointwise. -/
theorem classAvg_eq {X : Type*} {q c : ℕ} (hq : 0 < q) (hc : c < q) (w : ℕ → X → ℝ)
    (M N : ℕ) (x : X) :
    (((Ico M N).filter (fun n => n % q = c)).card : ℝ)⁻¹
        * ∑ n ∈ (Ico M N).filter (fun n => n % q = c), w n x
      = ((blockStart q c N - blockStart q c M : ℕ) : ℝ)⁻¹
        * ∑ a ∈ Ico (blockStart q c M) (blockStart q c N), w (q * a + c) x := by
  rw [card_class_eq hq hc, sum_class_eq hq hc (fun n => w n x)]

/-- **Undoing the re-indexing.**  A uniform limit of block averages `a ↦ w(q a + c)` gives the
same uniform limit for the averages over the residue class `n ≡ c mod q`. -/
theorem tendsto_classAvg {X : Type*} [MeasurableSpace X] {μ : Measure X} {q c : ℕ}
    (hq : 0 < q) (hc : c < q) (w : ℕ → X → ℝ)
    (h : Tendsto (fun p : ℕ × ℕ => eLpNorm
        (fun x => ((p.2 - p.1 : ℕ) : ℝ)⁻¹ * ∑ a ∈ Ico p.1 p.2, w (q * a + c) x) 2 μ)
      uniformFilter (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => eLpNorm
        (fun x => (((Ico p.1 p.2).filter (fun n => n % q = c)).card : ℝ)⁻¹
          * ∑ n ∈ (Ico p.1 p.2).filter (fun n => n % q = c), w n x) 2 μ)
      uniformFilter (𝓝 0) := by
  refine (h.comp (tendsto_blockStart hq hc)).congr fun p => ?_
  exact congrArg (fun g => eLpNorm g 2 μ) (funext fun x => (classAvg_eq hq hc w p.1 p.2 x).symm)

end CantorSzemeredi

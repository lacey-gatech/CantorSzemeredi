/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Cantor.Enum

/-!
# Differences along a shift, and residues

This file proves Lemma `lem:differences` and Lemma `lem:syndetic-residues` of the blueprint.

The content of `lem:differences` is that, once `δ^ℓ > h`, the difference `k_{n+h} - k_n`
depends only on `n mod δ^ℓ`, on the set of residues `c` with `c + h < δ^ℓ`; and that set of
indices has uniform density at least `1 - h δ^{-ℓ}`.

## Main results

* `CantorSzemeredi.CantorData.enum_sub_enum_eq` — `lem:differences`(i).
* `CantorSzemeredi.CantorData.card_goodResidues_ge` — `lem:differences`(ii).
* `CantorSzemeredi.CantorData.syndetic_dvd_enum` — `lem:syndetic-residues`.
-/

namespace CantorSzemeredi

namespace CantorData

variable (C : CantorData)

/-! ### Differences along a shift -/

/-- **Lemma `lem:differences`(i).**  If `n ≡ c mod δ^ℓ` and `c + h < δ^ℓ`, then
`k_{n+h} - k_n = k_{c+h} - k_c`: the difference depends only on the residue of `n`. -/
theorem enum_sub_enum_eq {ℓ h n c : ℕ} (hc : n % C.delta ^ ℓ = c) (hch : c + h < C.delta ^ ℓ) :
    (C.enum (n + h) : ℤ) - C.enum n = (C.enum (c + h) : ℤ) - C.enum c := by
  have hq : 0 < C.delta ^ ℓ := Nat.pow_pos (by have := C.two_le_delta; omega)
  set a := n / C.delta ^ ℓ with ha
  have hn : n = C.delta ^ ℓ * a + c := by
    rw [ha, ← hc]; exact (Nat.div_add_mod n _).symm
  have h1 : C.enum n = C.base ^ ℓ * C.enum a + C.enum c := by
    rw [hn]; exact C.enum_block ℓ a (by omega)
  have h2 : C.enum (n + h) = C.base ^ ℓ * C.enum a + C.enum (c + h) := by
    rw [show n + h = C.delta ^ ℓ * a + (c + h) by omega]
    exact C.enum_block ℓ a hch
  rw [h1, h2]
  push_cast
  ring

/-! ### A counting bound for the good residues -/

/-- Shifting is injective on residues: `r ↦ (M + r) mod q` is injective on `[0, q)`. -/
private theorem add_mod_injOn {q M r₁ r₂ : ℕ} (h₁ : r₁ < q) (h₂ : r₂ < q)
    (h : (M + r₁) % q = (M + r₂) % q) : r₁ = r₂ := by
  have : r₁ % q = r₂ % q := Nat.ModEq.add_left_cancel' M h
  rwa [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at this

/-- At most `h` residues mod `q` are "bad", i.e. satisfy `q ≤ c + h`. -/
private theorem card_badShifted_le {q h : ℕ} (hhq : h ≤ q) (M : ℕ) :
    ((Finset.range q).filter (fun r => q ≤ (M + r) % q + h)).card ≤ h := by
  have hcard : (Finset.Ico (q - h) q).card = h := by rw [Nat.card_Ico]; omega
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun r => (M + r) % q) ?_ ?_
  · intro r hr
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hr
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact absurd hr.1 (by omega)
    · simp only [Finset.mem_coe, Finset.mem_Ico]
      exact ⟨by omega, Nat.mod_lt _ hq⟩
  · intro r₁ h₁ r₂ h₂ he
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at h₁ h₂
    exact add_mod_injOn h₁.1 h₂.1 he

/-- **Lemma `lem:differences`(ii).**  Writing `q = δ^ℓ`, the set of indices
`ℙ = {n : n mod q + h < q}` — on which, by `enum_sub_enum_eq`, the difference `k_{n+h} - k_n`
is a function of `n mod q` alone — satisfies
`|ℙ ∩ [M, N)| ≥ (1 - h/q)(N - M) - q` for every interval `[M, N)`. -/
theorem card_goodResidues_ge (h ℓ M N : ℕ) (hlt : h < C.delta ^ ℓ) :
    (1 - (h : ℝ) / (C.delta : ℝ) ^ ℓ) * ((N : ℝ) - M) - (C.delta : ℝ) ^ ℓ ≤
      (((Finset.Ico M N).filter (fun n => n % C.delta ^ ℓ + h < C.delta ^ ℓ)).card : ℝ) := by
  set q := C.delta ^ ℓ with hqdef
  have hq : 0 < q := Nat.pow_pos (by have := C.two_le_delta; omega)
  -- The bad set is the complement of the good set inside `[M, N)`.
  set good := (Finset.Ico M N).filter (fun n => n % q + h < q) with hgood
  set bad := (Finset.Ico M N).filter (fun n => ¬ (n % q + h < q)) with hbad
  have hsplit : good.card + bad.card = N - M := by
    rw [hgood, hbad, Finset.card_filter_add_card_filter_not, Nat.card_Ico]
  -- `bad` injects into `range ((N - M) / q + 1) ×ˢ (bad residues)`.
  set B := (Finset.range q).filter (fun r => q ≤ (M + r) % q + h) with hB
  have hbadle : bad.card ≤ ((N - M) / q + 1) * h := by
    calc bad.card ≤ (Finset.range ((N - M) / q + 1) ×ˢ B).card := by
          refine Finset.card_le_card_of_injOn (fun n => ((n - M) / q, (n - M) % q)) ?_ ?_
          · intro n hn
            simp only [hbad, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico] at hn
            simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, hB,
              Finset.mem_filter]
            have hshift : (M + (n - M) % q) % q = n % q := by
              have hmod := (Nat.mod_modEq (n - M) q).add_left M
              rw [show M + (n - M) = n by omega] at hmod
              exact hmod
            refine ⟨?_, Nat.mod_lt _ hq, ?_⟩
            · have : n - M < N - M := by omega
              exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
            · rw [hshift]; omega
          · intro n₁ h₁ n₂ h₂ he
            simp only [hbad, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico] at h₁ h₂
            have he1 : (n₁ - M) / q = (n₂ - M) / q := congrArg Prod.fst he
            have he2 : (n₁ - M) % q = (n₂ - M) % q := congrArg Prod.snd he
            have e₁ := Nat.div_add_mod (n₁ - M) q
            have e₂ := Nat.div_add_mod (n₂ - M) q
            have : n₁ - M = n₂ - M := by rw [← e₁, ← e₂, he1, he2]
            omega
      _ = ((N - M) / q + 1) * B.card := by rw [Finset.card_product, Finset.card_range]
      _ ≤ ((N - M) / q + 1) * h :=
          Nat.mul_le_mul_left _ (card_badShifted_le (by omega) M)
  -- Turn the bounds into real arithmetic.
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqpow : ((C.delta : ℝ)) ^ ℓ = (q : ℝ) := by rw [hqdef]; push_cast; ring
  have hNM : ((N : ℝ) - M) ≤ ((N - M : ℕ) : ℝ) := by
    rcases le_or_gt M N with hle | hgt
    · rw [Nat.cast_sub hle]
    · have h0 : ((N - M : ℕ) : ℝ) = 0 := by
        rw [Nat.sub_eq_zero_of_le hgt.le]; simp
      have h1 : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hgt.le
      rw [h0]; linarith
  have hhq : (h : ℝ) ≤ (q : ℝ) := by exact_mod_cast hlt.le
  have hdiv : (((N - M) / q : ℕ) : ℝ) ≤ ((N - M : ℕ) : ℝ) / (q : ℝ) := by
    rw [le_div_iff₀ hqR]
    exact_mod_cast Nat.div_mul_le_self _ _
  have hbadR : (bad.card : ℝ) ≤ ((N - M : ℕ) : ℝ) * (h : ℝ) / (q : ℝ) + h := by
    have hc := (Nat.cast_le (α := ℝ)).2 hbadle
    push_cast at hc
    have hm := mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg (α := ℝ) h)
    have hr : ((N - M : ℕ) : ℝ) / q * h = ((N - M : ℕ) : ℝ) * h / q := by ring
    nlinarith [hm, hr]
  have hgoodR : ((N - M : ℕ) : ℝ) - (((N - M : ℕ) : ℝ) * h / q + h) ≤ (good.card : ℝ) := by
    have hs : (good.card : ℝ) + (bad.card : ℝ) = ((N - M : ℕ) : ℝ) := by exact_mod_cast hsplit
    linarith
  have hcoef : (0 : ℝ) ≤ 1 - (h : ℝ) / q := by rw [sub_nonneg, div_le_one hqR]; exact hhq
  have hterm : (1 - (h : ℝ) / q) * ((N : ℝ) - M) ≤ (1 - (h : ℝ) / q) * ((N - M : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hNM hcoef
  have hexp : (1 - (h : ℝ) / q) * ((N - M : ℕ) : ℝ) =
      ((N - M : ℕ) : ℝ) - ((N - M : ℕ) : ℝ) * h / q := by field_simp
  rw [hqpow]
  linarith

/-! ### Syndetic residues -/

/-- **Lemma `lem:syndetic-residues`.**  For every `q ≥ 1` the set `{n : q ∣ k_n}` is syndetic.

This lemma is used only for the roots-of-unity form of the compact extension theorem, which
is not needed for the main theorem. -/
theorem syndetic_dvd_enum (q : ℕ) (hq : 0 < q) : Syndetic {n | q ∣ C.enum n} := by
  sorry

end CantorData

end CantorSzemeredi

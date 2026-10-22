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

/-! ### Syndetic residues

The proof of `syndetic_dvd_enum` below is a streamlined version of the blueprint's argument.
Work in `ZMod q` and write
`R i = {k_j mod q : j < δ^i}`,  `A c = {d b^c mod q : d ∈ D}`.
Splitting `j < δ^(i+1)` as `j = δ^i c + j'` with `c < δ` and `j' < δ^i` gives
`R (i+1) = R i + A i`.  Since `0 ∈ A i`, the `R i` increase, so they stabilise to some `W`
at some `i₀`, and then `W + A i = W` for every `i ≥ i₀`.  Hence every `A i` with `i ≥ i₀` lies
in the stabiliser subgroup `Stab = {t | W + t = W}`, which is contained in `W` because
`0 ∈ W`.  Expanding `b^i k_n` along the recursion `enum_eq` exhibits it as a sum of elements
of such `A`'s, so `-(b^i k_n) ∈ Stab ⊆ W = R i`: there is `j < δ^i` with
`k_j ≡ -b^i k_n`, and then `q ∣ k_{δ^i n + j}` by `enum_block`.  This meets every block
`[δ^i n, δ^i (n+1))`, so the gaps are at most `2 δ^i`.

Unlike the blueprint's argument this needs no eventual periodicity of `b^c mod q`: the
stabilisation of the `R i` already supplies everything. -/

open scoped Pointwise

/-- `R i = {k_j mod q : j < δ^i}`, the residues reachable within one block of length `δ^i`. -/
private noncomputable def residues (q i : ℕ) : Finset (ZMod q) :=
  (Finset.range (C.delta ^ i)).image fun j : ℕ => (C.enum j : ZMod q)

/-- `A c = {d b^c mod q : d ∈ D}`, the contributions of the digit in position `c`. -/
private noncomputable def digitSet (q c : ℕ) : Finset (ZMod q) :=
  C.digits.image fun d : ℕ => (d : ZMod q) * (C.base : ZMod q) ^ c

private theorem zero_mem_digitSet (q c : ℕ) : (0 : ZMod q) ∈ C.digitSet q c :=
  Finset.mem_image.2 ⟨0, C.zero_mem, by simp⟩

private theorem zero_mem_residues (q i : ℕ) : (0 : ZMod q) ∈ C.residues q i :=
  Finset.mem_image.2 ⟨0, Finset.mem_range.2 (Nat.pow_pos (by have := C.two_le_delta; omega)),
    by simp⟩

/-- Peeling off the top base-`δ` digit: `R (i+1) = R i + A i`. -/
private theorem residues_succ (q i : ℕ) :
    C.residues q (i + 1) = C.residues q i + C.digitSet q i := by
  have hδ : 0 < C.delta ^ i := Nat.pow_pos (by have := C.two_le_delta; omega)
  have hpow : C.delta ^ (i + 1) = C.delta ^ i * C.delta := by ring
  ext x
  simp only [residues, digitSet, Finset.mem_image, Finset.mem_range, Finset.mem_add]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hc : j / C.delta ^ i < C.delta := by
      rw [Nat.div_lt_iff_lt_mul hδ]
      calc j < C.delta ^ (i + 1) := hj
        _ = C.delta * C.delta ^ i := by ring
    have hm : j % C.delta ^ i < C.delta ^ i := Nat.mod_lt _ hδ
    have hsplit : C.delta ^ i * (j / C.delta ^ i) + j % C.delta ^ i = j := Nat.div_add_mod j _
    have hval : C.enum j = C.base ^ i * C.digit (j / C.delta ^ i) + C.enum (j % C.delta ^ i) := by
      conv_lhs => rw [← hsplit]
      rw [C.enum_block i (j / C.delta ^ i) hm, C.enum_eq_digit hc]
    refine ⟨(C.enum (j % C.delta ^ i) : ZMod q), ⟨j % C.delta ^ i, hm, rfl⟩,
      ((C.digit (j / C.delta ^ i) : ZMod q) * (C.base : ZMod q) ^ i),
      ⟨C.digit (j / C.delta ^ i), C.digit_mem hc, rfl⟩, ?_⟩
    rw [hval]
    push_cast
    ring
  · rintro ⟨-, ⟨j', hj', rfl⟩, -, ⟨d, hd, rfl⟩, rfl⟩
    have hid := C.index_lt hd
    refine ⟨C.delta ^ i * C.index d + j', ?_, ?_⟩
    · rw [hpow]; nlinarith
    · rw [C.enum_block i (C.index d) hj', C.enum_eq_digit hid, C.digit_index hd]
      push_cast
      ring

private theorem residues_subset_succ (q i : ℕ) : C.residues q i ⊆ C.residues q (i + 1) := by
  rw [residues_succ]
  intro x hx
  exact Finset.mem_add.2 ⟨x, hx, 0, C.zero_mem_digitSet q i, by simp⟩

private theorem residues_mono (q : ℕ) : Monotone (C.residues q) :=
  monotone_nat_of_le_succ fun i => C.residues_subset_succ q i

/-- The residue sets `R i` increase inside the finite set `ZMod q`, hence stabilise. -/
private theorem exists_residues_stable (q : ℕ) [NeZero q] :
    ∃ i₀, ∀ i, i₀ ≤ i → C.residues q i = C.residues q i₀ := by
  have hne : (Set.range fun i => (C.residues q i).card).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hbdd : BddAbove (Set.range fun i => (C.residues q i).card) :=
    ⟨Fintype.card (ZMod q), by rintro _ ⟨i, rfl⟩; exact Finset.card_le_univ _⟩
  obtain ⟨i₀, hi₀⟩ := Nat.sSup_mem hne hbdd
  refine ⟨i₀, fun i hi => ?_⟩
  exact (Finset.eq_of_subset_of_card_le (C.residues_mono q hi)
    (le_of_le_of_eq (le_csSup hbdd ⟨i, rfl⟩) hi₀.symm)).symm

/-- The subgroup of translations preserving a finite set `W ⊆ ZMod q`. -/
private def transStab {q : ℕ} (W : Finset (ZMod q)) : AddSubgroup (ZMod q) where
  carrier := {t | W.image (· + t) = W}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    have h : (fun x : ZMod q => x + 0) = id := by funext x; simp
    rw [h, Finset.image_id]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have h : (W.image (fun x : ZMod q => x + a)).image (fun x => x + b)
        = W.image (fun x => x + (a + b)) := by
      rw [Finset.image_image]
      congr 1
      funext x
      simp [Function.comp, add_assoc]
    rw [← h, ha, hb]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [Finset.image_image]
    have h : ((fun x : ZMod q => x + -a) ∘ (fun x => x + a)) = id := by funext x; simp
    rw [h, Finset.image_id]

private theorem mem_transStab {q : ℕ} {W : Finset (ZMod q)} {t : ZMod q} :
    t ∈ transStab W ↔ W.image (· + t) = W := Iff.rfl

/-- **Lemma `lem:syndetic-residues`.**  For every `q ≥ 1` the set `{n : q ∣ k_n}` is syndetic.

This lemma is used only for the roots-of-unity form of the compact extension theorem, which
is not needed for the main theorem. -/
theorem syndetic_dvd_enum (q : ℕ) (hq : 0 < q) : Syndetic {n | q ∣ C.enum n} := by
  have : NeZero q := ⟨by omega⟩
  have hδ : 2 ≤ C.delta := C.two_le_delta
  obtain ⟨i₀, hstab⟩ := C.exists_residues_stable q
  set W := C.residues q i₀ with hW
  -- Every `A i` with `i ≥ i₀` translates `W` to itself.
  have hA : ∀ i, i₀ ≤ i → ∀ a ∈ C.digitSet q i, a ∈ transStab W := by
    intro i hi a ha
    have h1 : W + C.digitSet q i = W :=
      calc W + C.digitSet q i = C.residues q i + C.digitSet q i := by rw [hstab i hi]
        _ = C.residues q (i + 1) := (C.residues_succ q i).symm
        _ = W := hstab (i + 1) (by omega)
    refine Finset.eq_of_subset_of_card_le ?_
      (le_of_eq (Finset.card_image_of_injective _ (add_left_injective a)).symm)
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [← h1]
    exact Finset.mem_add.2 ⟨y, hy, a, ha, rfl⟩
  -- Expanding `b^i k_n` along `enum_eq` puts it in the stabiliser.
  have hkey : ∀ n i, i₀ ≤ i → ((C.enum n : ZMod q) * (C.base : ZMod q) ^ i) ∈ transStab W := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hmem : ((C.digit (n % C.delta) : ZMod q) * (C.base : ZMod q) ^ i) ∈ transStab W :=
          hA i hi _ (Finset.mem_image.2
            ⟨_, C.digit_mem (Nat.mod_lt _ (by omega)), rfl⟩)
        have hih := ih (n / C.delta) (Nat.div_lt_self hn (by omega)) (i + 1) (by omega)
        have hexp : (C.enum n : ZMod q) * (C.base : ZMod q) ^ i
            = ((C.digit (n % C.delta) : ZMod q) * (C.base : ZMod q) ^ i)
              + ((C.enum (n / C.delta) : ZMod q) * (C.base : ZMod q) ^ (i + 1)) := by
          rw [C.enum_eq n]; push_cast; ring
        rw [hexp]
        exact (transStab W).add_mem hmem hih
  have hsubW : ∀ t, t ∈ transStab W → t ∈ W := by
    intro t ht
    have hm : t ∈ W.image (· + t) :=
      Finset.mem_image.2 ⟨0, C.zero_mem_residues q i₀, by simp⟩
    rwa [mem_transStab.1 ht] at hm
  -- Conclusion: the good set meets every block `[δ^i₀ n, δ^i₀ (n+1))`.
  have hQ0 : 0 < C.delta ^ i₀ := Nat.pow_pos (by omega)
  refine ⟨2 * C.delta ^ i₀, fun N => ?_⟩
  set Q := C.delta ^ i₀ with hQ
  set n := N / Q + 1 with hndef
  have hmul : Q * n = Q * (N / Q) + Q := by rw [hndef]; ring
  have hdm := Nat.div_add_mod N Q
  have hmodlt : N % Q < Q := Nat.mod_lt _ hQ0
  have hres := hsubW _ ((transStab W).neg_mem
    (show ((C.base : ZMod q) ^ i₀ * (C.enum n : ZMod q)) ∈ transStab W by
      rw [mul_comm]; exact hkey n i₀ le_rfl))
  rw [hW, residues, ← hQ] at hres
  obtain ⟨j, hj, hje⟩ := Finset.mem_image.1 hres
  rw [Finset.mem_range] at hj
  have hdvd : q ∣ C.enum (Q * n + j) := by
    rw [← ZMod.natCast_eq_zero_iff, C.enum_block i₀ n hj]
    push_cast
    rw [hje]
    ring
  exact ⟨Q * n + j, hdvd, by omega, by omega⟩

end CantorData

end CantorSzemeredi

/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Basic

/-!
# Integer Cantor sets

The blueprint (`blueprint/src/chapter/cantor.tex`) recommends *defining* the increasing
enumeration of `C_{b,D}` by the digit-transfer map of Lemma `lem:diff`(i), rather than by
"the `n`-th smallest element", and then proving that this map is a strictly monotone
bijection onto `C_{b,D}`.  That is what is set up here.
-/

namespace CantorSzemeredi

/-- The data of an integer Cantor set: a base `b ≥ 3` and a digit set `D ⊆ {0, …, b-1}`
containing `0`, with `2 ≤ |D| < b`. -/
structure CantorData where
  /-- The base. -/
  base : ℕ
  /-- The digit set. -/
  digits : Finset ℕ
  three_le_base : 3 ≤ base
  zero_mem : 0 ∈ digits
  digits_lt_base : ∀ d ∈ digits, d < base
  two_le_card : 2 ≤ digits.card
  card_lt_base : digits.card < base

namespace CantorData

variable (C : CantorData)

/-- `δ = |D|`, the base in which the enumeration index is written. -/
def delta : ℕ := C.digits.card

/-- The `c`-th smallest allowed digit, `d_c`; `d_0 = 0`. -/
noncomputable def digit (c : ℕ) : ℕ :=
  (C.digits.sort (· ≤ ·)).getD c 0

/-- The digit-transfer map `φ : ℕ₀ → ℕ₀`: write `n` in base `δ` and replace each digit `c`
by `d_c`, read in base `b`.  By Lemma `lem:diff`(i) this is the increasing enumeration
`n ↦ k_n` of the Cantor set. -/
noncomputable def enum (n : ℕ) : ℕ :=
  Nat.ofDigits C.base ((Nat.digits C.delta n).map C.digit)

/-- The integer Cantor set itself, as the range of the enumeration. -/
noncomputable def set : Set ℕ := Set.range C.enum

/-- `δ ≥ 2`. -/
theorem two_le_delta : 2 ≤ C.delta := C.two_le_card

/-- `1 < δ`, the form needed by `Nat.digits_def'`. -/
theorem one_lt_delta : 1 < C.delta := C.two_le_card

/-- `δ < b`. -/
theorem delta_lt_base : C.delta < C.base := C.card_lt_base

/-- The sorted list of allowed digits has length `δ`. -/
theorem length_sortedDigits : (C.digits.sort (· ≤ ·)).length = C.delta :=
  Finset.length_sort _

/-- Below `δ`, `digit` reads off an element of the digit set. -/
theorem digit_mem {c : ℕ} (hc : c < C.delta) : C.digit c ∈ C.digits := by
  have h : c < (C.digits.sort (· ≤ ·)).length := by rwa [C.length_sortedDigits]
  rw [digit, List.getD_eq_getElem _ _ h, ← Finset.mem_sort (· ≤ ·)]
  exact List.getElem_mem h

/-- Allowed digits are `< b`. -/
theorem digit_lt_base {c : ℕ} (hc : c < C.delta) : C.digit c < C.base :=
  C.digits_lt_base _ (C.digit_mem hc)

/-- `c ↦ d_c` is strictly increasing on `[0, δ)`. -/
theorem digit_lt_digit {c₁ c₂ : ℕ} (h : c₁ < c₂) (hc₂ : c₂ < C.delta) :
    C.digit c₁ < C.digit c₂ := by
  have h₂ : c₂ < (C.digits.sort (· ≤ ·)).length := by rwa [C.length_sortedDigits]
  have h₁ : c₁ < (C.digits.sort (· ≤ ·)).length := h.trans h₂
  rw [digit, digit, List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂]
  exact (Finset.sortedLT_sort C.digits).getElem_lt_getElem_of_lt h

/-- `d_0 = 0`, since `0 ∈ D`. -/
@[simp] theorem digit_zero : C.digit 0 = 0 := by
  set l := C.digits.sort (· ≤ ·) with hl
  have hmem : (0 : ℕ) ∈ l := (Finset.mem_sort _).2 C.zero_mem
  have hk : l.idxOf 0 < l.length := List.idxOf_lt_length_of_mem hmem
  have hdz : C.digit (l.idxOf 0) = 0 := by
    rw [digit, ← hl, List.getD_eq_getElem _ _ hk]
    exact List.getElem_idxOf hk
  rcases Nat.eq_zero_or_pos (l.idxOf 0) with h0 | hpos
  · rwa [h0] at hdz
  · exfalso
    have h2 := C.digit_lt_digit hpos (by rw [← C.length_sortedDigits]; exact hk)
    rw [hdz] at h2
    omega

/-- `d_c ≥ 1` for `1 ≤ c < δ`. -/
theorem one_le_digit {c : ℕ} (hc : 0 < c) (hcd : c < C.delta) : 1 ≤ C.digit c := by
  have := C.digit_lt_digit hc hcd
  simp only [digit_zero] at this
  omega

/-- The index `ι(d) < δ` of an allowed digit `d`. -/
noncomputable def index (d : ℕ) : ℕ := (C.digits.sort (· ≤ ·)).idxOf d

/-- The index of an allowed digit is `< δ`. -/
theorem index_lt {d : ℕ} (hd : d ∈ C.digits) : C.index d < C.delta := by
  rw [← C.length_sortedDigits]
  exact List.idxOf_lt_length_of_mem ((Finset.mem_sort _).2 hd)

/-- `index` is a right inverse of `digit` on the digit set. -/
@[simp] theorem digit_index {d : ℕ} (hd : d ∈ C.digits) : C.digit (C.index d) = d := by
  have h : (C.digits.sort (· ≤ ·)).idxOf d < (C.digits.sort (· ≤ ·)).length :=
    List.idxOf_lt_length_of_mem ((Finset.mem_sort _).2 hd)
  rw [digit, index, List.getD_eq_getElem _ _ h]
  exact List.getElem_idxOf h

@[simp] theorem enum_zero : C.enum 0 = 0 := by simp [enum]

/-- **The defining recursion of the enumeration.**  Peeling off the last base-`δ` digit of
`n` gives the last base-`b` digit of `k_n`:
`k_n = d_{n mod δ} + b * k_{n / δ}`.  Valid for all `n`, including `n = 0`. -/
theorem enum_eq (n : ℕ) : C.enum n = C.digit (n % C.delta) + C.base * C.enum (n / C.delta) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.zero_div]
  · rw [enum, Nat.digits_def' C.one_lt_delta hn, List.map_cons, Nat.ofDigits_cons, enum]

/-- `k_n`'s last base-`b` digit, `d_{n mod δ}`, is `< b`. -/
theorem digit_mod_lt_base (n : ℕ) : C.digit (n % C.delta) < C.base :=
  C.digit_lt_base (Nat.mod_lt _ (by have := C.two_le_delta; omega))

end CantorData

end CantorSzemeredi

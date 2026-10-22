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

end CantorData

end CantorSzemeredi

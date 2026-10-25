/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Cantor.Enum

/-!
# Disjoint digit ranges add

Blueprint: `blueprint/src/chapter/vdw.tex`, `lem:digit-ranges`.  Sums of elements of `b^h Cantor`
and `b^{h'} Cantor` with `h ≤ h'` and the first summand below `b^{h'}` stay in `b^h Cantor`.
-/

namespace CantorSzemeredi

namespace CantorData

/-- **Lemma `lem:digit-ranges`.**  Let `h ≤ h'`, `a ∈ b^h Cantor` with `a < b^{h'}`, and
`c ∈ b^{h'} Cantor`.  Then `a + c ∈ b^h Cantor`. -/
theorem pow_mul_add_mem_of_lt_pow (C : CantorData) {h h' a c : ℕ} (hhh : h ≤ h')
    (ha : ∃ m ∈ C.set, a = C.base ^ h * m) (hab : a < C.base ^ h')
    (hc : ∃ m ∈ C.set, c = C.base ^ h' * m) :
    ∃ m ∈ C.set, a + c = C.base ^ h * m := by
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨u, rfl⟩ := hc'
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hhh
  have hpos : 0 < C.base ^ h := pow_pos (by have := C.three_le_base; omega) h
  have hlt : a' < C.base ^ d := by
    rw [pow_add] at hab
    exact Nat.lt_of_mul_lt_mul_left hab
  refine ⟨C.base ^ d * C.enum u + a', C.pow_mul_enum_add_mem ha' hlt u, ?_⟩
  rw [pow_add]
  ring

end CantorData

end CantorSzemeredi

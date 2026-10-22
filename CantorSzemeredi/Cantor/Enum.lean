/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Cantor.Defs

/-!
# The block structure of the Cantor enumeration

This file proves Lemma `lem:diff` of the blueprint and its two corollaries.

Part (i) of `lem:diff` is true by definition here: `CantorData.enum` *is* the digit-transfer
map.  What has to be proved is that this map is the increasing enumeration of `C_{b,D}`, which
is `CantorData.enum_strictMono` together with `CantorData.mem_set_iff`.

Part (ii), `CantorData.enum_block`, is the keystone of the whole project:
`k_{δ^i n + j} = b^i k_n + k_j` for `j < δ^i`.  Everything else in the Cantor-set chapter
follows from it.

## Main results

* `CantorSzemeredi.CantorData.enum_strictMono` — `n ↦ k_n` is strictly increasing.
* `CantorSzemeredi.CantorData.mem_set_iff` — the range of `enum` is exactly the set of
  base-`b` expansions with all digits in `D`.
* `CantorSzemeredi.CantorData.enum_block` — `k_{δ^i n + j} = b^i k_n + k_j` for `j < δ^i`.
* `CantorSzemeredi.CantorData.enum_pow_mul`, `CantorSzemeredi.CantorData.pow_mul_mem` —
  self-similarity, `cor:self-similar`.
* `CantorSzemeredi.CantorData.enum_add_mem_block` — absorption, `cor:absorb`.
-/

namespace CantorSzemeredi

namespace CantorData

variable (C : CantorData)

/-! ### Monotonicity and the range -/

/-- The enumeration is strictly increasing: `k_0 < k_1 < ⋯`.  This, with `mem_set_iff`, is
Lemma `lem:diff`(i): `enum` really is the increasing enumeration of `C_{b,D}`. -/
theorem enum_strictMono : StrictMono C.enum := by
  intro n m hnm
  induction m using Nat.strong_induction_on generalizing n with
  | _ m ih =>
    have hδ := C.two_le_delta
    have hm : 0 < m := by omega
    rw [C.enum_eq n, C.enum_eq m]
    rcases lt_or_eq_of_le (Nat.div_le_div_right (le_of_lt hnm) : n / C.delta ≤ m / C.delta) with
      hdiv | hdiv
    · have hlt : C.enum (n / C.delta) < C.enum (m / C.delta) :=
        ih (m / C.delta) (Nat.div_lt_self hm (by omega)) hdiv
      have h1 : C.digit (n % C.delta) < C.base := C.digit_mod_lt_base n
      have h2 : C.base * (C.enum (n / C.delta) + 1) ≤ C.base * C.enum (m / C.delta) :=
        Nat.mul_le_mul_left _ hlt
      nlinarith [Nat.zero_le (C.digit (m % C.delta))]
    · rw [hdiv]
      have hmod : n % C.delta < m % C.delta := by
        have hn := Nat.div_add_mod n C.delta
        have hm' := Nat.div_add_mod m C.delta
        rw [hdiv] at hn
        omega
      have := C.digit_lt_digit hmod (Nat.mod_lt _ (by omega))
      omega

/-- `enum` is injective. -/
theorem enum_injective : Function.Injective C.enum := C.enum_strictMono.injective

/-- Appending a digit: `k_{δ n + c} = d_c + b k_n` for `c < δ`. -/
theorem enum_mul_add {n c : ℕ} (hc : c < C.delta) :
    C.enum (C.delta * n + c) = C.digit c + C.base * C.enum n := by
  have hδ : 0 < C.delta := by have := C.two_le_delta; omega
  rw [C.enum_eq (C.delta * n + c), Nat.mul_add_mod, Nat.mod_eq_of_lt hc,
    Nat.mul_add_div hδ, Nat.div_eq_of_lt hc, Nat.add_zero]

/-- Below `δ` the enumeration is just the digit map: `k_c = d_c`. -/
theorem enum_eq_digit {c : ℕ} (hc : c < C.delta) : C.enum c = C.digit c := by
  rw [C.enum_eq c, Nat.mod_eq_of_lt hc, Nat.div_eq_of_lt hc, enum_zero, Nat.mul_zero, Nat.add_zero]

/-- The range of the enumeration is exactly the set of numbers all of whose base-`b` digits
(in some finite expansion) lie in `D`.  This is the original Definition `def:cantor`. -/
theorem mem_set_iff {m : ℕ} :
    m ∈ C.set ↔ ∃ L : List ℕ, (∀ d ∈ L, d ∈ C.digits) ∧ m = Nat.ofDigits C.base L := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨(Nat.digits C.delta n).map C.digit, ?_, rfl⟩
    intro d hd
    simp only [List.mem_map] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    exact C.digit_mem (Nat.digits_lt_base C.one_lt_delta hc)
  · rintro ⟨L, hL, rfl⟩
    induction L with
    | nil => exact ⟨0, by simp [Nat.ofDigits]⟩
    | cons d L ih =>
      obtain ⟨n, hn⟩ := ih fun x hx => hL x (List.mem_cons_of_mem _ hx)
      have hd : d ∈ C.digits := hL d List.mem_cons_self
      refine ⟨C.delta * n + C.index d, ?_⟩
      rw [C.enum_mul_add (C.index_lt hd), C.digit_index hd, hn, Nat.ofDigits_cons]

/-! ### The keystone -/

/-- **Lemma `lem:diff`(ii).**  For `0 ≤ j < δ^i`,
`k_{δ^i n + j} = b^i k_n + k_j`.

This is the keystone of the paper: the enumeration of a Cantor set is built out of blocks of
length `δ^i`, on each of which it is a translate of its own first `δ^i` values, scaled by
`b^i`. -/
theorem enum_block (i n : ℕ) {j : ℕ} (hj : j < C.delta ^ i) :
    C.enum (C.delta ^ i * n + j) = C.base ^ i * C.enum n + C.enum j := by
  have hδ : 0 < C.delta := by have := C.two_le_delta; omega
  induction i generalizing j n with
  | zero =>
    obtain rfl : j = 0 := by simpa using hj
    simp
  | succ i ih =>
    have hjd : j / C.delta < C.delta ^ i := by
      rw [Nat.div_lt_iff_lt_mul hδ]
      calc j < C.delta ^ (i + 1) := hj
        _ = C.delta ^ i * C.delta := by ring
    have hmod : (C.delta ^ (i + 1) * n + j) % C.delta = j % C.delta := by
      rw [pow_succ, mul_comm (C.delta ^ i) C.delta, mul_assoc, Nat.mul_add_mod]
    have hdiv : (C.delta ^ (i + 1) * n + j) / C.delta = C.delta ^ i * n + j / C.delta := by
      rw [pow_succ, mul_comm (C.delta ^ i) C.delta, mul_assoc, Nat.mul_add_div hδ]
    rw [C.enum_eq (C.delta ^ (i + 1) * n + j), hmod, hdiv, ih _ hjd, C.enum_eq j]
    ring

/-! ### Corollaries -/

/-- **Corollary `cor:self-similar`.**  `b^i k_n = k_{δ^i n}`. -/
theorem enum_pow_mul (i n : ℕ) : C.enum (C.delta ^ i * n) = C.base ^ i * C.enum n := by
  simpa using C.enum_block i n (j := 0) (Nat.pow_pos (by have := C.two_le_delta; omega))

/-- **Corollary `cor:self-similar`.**  `b^i C ⊆ C`. -/
theorem pow_mul_mem (i : ℕ) {m : ℕ} (hm : m ∈ C.set) : C.base ^ i * m ∈ C.set := by
  obtain ⟨n, rfl⟩ := hm
  exact ⟨C.delta ^ i * n, C.enum_pow_mul i n⟩

/-- If `n < δ^i` then `k_n < b^i`. -/
theorem enum_lt_pow {i n : ℕ} (hn : n < C.delta ^ i) : C.enum n < C.base ^ i := by
  have hδ : 0 < C.delta := by have := C.two_le_delta; omega
  induction i generalizing n with
  | zero =>
    obtain rfl : n = 0 := by simpa using hn
    simp
  | succ i ih =>
    have hnd : n / C.delta < C.delta ^ i := by
      rw [Nat.div_lt_iff_lt_mul hδ]
      calc n < C.delta ^ (i + 1) := hn
        _ = C.delta ^ i * C.delta := by ring
    have h1 := ih hnd
    have h2 := C.digit_mod_lt_base n
    rw [C.enum_eq n, pow_succ]
    nlinarith [Nat.one_le_iff_ne_zero.2 (show C.base ≠ 0 by have := C.three_le_base; omega)]

/-- `k_{δ^i} ≥ b^i`; the converse direction to `enum_lt_pow`. -/
theorem pow_le_enum_pow (i : ℕ) : C.base ^ i ≤ C.enum (C.delta ^ i) := by
  have h1 : C.enum (C.delta ^ i * 1) = C.base ^ i * C.enum 1 := C.enum_pow_mul i 1
  have h2 : 1 ≤ C.enum 1 := by
    have hδ := C.two_le_delta
    rw [C.enum_eq 1, Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
    have := C.one_le_digit (c := 1) (by omega) (by omega)
    omega
  calc C.base ^ i = C.base ^ i * 1 := by ring
    _ ≤ C.base ^ i * C.enum 1 := Nat.mul_le_mul_left _ h2
    _ = C.enum (C.delta ^ i * 1) := h1.symm
    _ = C.enum (C.delta ^ i) := by ring_nf

/-- `k_n < b^i` exactly when `n < δ^i`: the first `δ^i` elements of `C` are exactly those
below `b^i`. -/
theorem enum_lt_pow_iff {i n : ℕ} : C.enum n < C.base ^ i ↔ n < C.delta ^ i := by
  refine ⟨fun h => ?_, C.enum_lt_pow⟩
  by_contra hn
  push Not at hn
  exact absurd (le_trans (C.pow_le_enum_pow i) (C.enum_strictMono.monotone hn)) (by omega)

/-- **Corollary `cor:absorb`.**  If `a ∈ C ∩ [0, b^i)` has index `ι(a) < δ^i`, then for every
`u`, `b^i k_u + a = k_{δ^i u + ι(a)}`, and that index lies in the block
`[δ^i u, δ^i (u+1))`. -/
theorem enum_add_mem_block {i : ℕ} {a : ℕ} (ha : a ∈ C.set) (halt : a < C.base ^ i) (u : ℕ) :
    ∃ v, C.delta ^ i * u ≤ v ∧ v < C.delta ^ i * (u + 1) ∧
      C.enum v = C.base ^ i * C.enum u + a := by
  obtain ⟨t, rfl⟩ := ha
  have ht : t < C.delta ^ i := C.enum_lt_pow_iff.1 halt
  exact ⟨C.delta ^ i * u + t, by omega, by nlinarith, C.enum_block i u ht⟩

/-- The absorption statement in the form used later: `b^i k_u + a ∈ C`. -/
theorem pow_mul_enum_add_mem {i : ℕ} {a : ℕ} (ha : a ∈ C.set) (halt : a < C.base ^ i) (u : ℕ) :
    C.base ^ i * C.enum u + a ∈ C.set := by
  obtain ⟨v, -, -, hv⟩ := C.enum_add_mem_block ha halt u
  exact ⟨v, hv⟩

end CantorData

end CantorSzemeredi

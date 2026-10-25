/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.VdW.Digits
import CantorSzemeredi.VdW.Minimal

/-!
# Colour focusing

Blueprint: `blueprint/src/chapter/vdw.tex`, `lem:color-focusing`.  In a minimal system, with a finite
cover of the form `T^{-n}U`, one builds points `x_j` with colours `α_j` and gaps `k_l` such that the
partial sums `σ(j,j') = k_{j+1} + ⋯ + k_{j'}` lie in `b^h Cantor \ {0}`, with `T^{α_j} x_j ∈ U`, and
the progression conditions along the sums.
-/

namespace CantorSzemeredi

open Set Finset Filter Topology

namespace CantorData

/-- `r` is an element of `b^h Cantor`. -/
def Dig (C : CantorData) (h r : ℕ) : Prop := ∃ m ∈ C.set, r = C.base ^ h * m

/-- The partial sum `k_{j+1} + ⋯ + k_{j'}`. -/
def sigmaSum (k : ℕ → ℕ) (j j' : ℕ) : ℕ := ∑ l ∈ Ioc j j', k l

theorem sigmaSum_succ (k : ℕ → ℕ) {j J : ℕ} (hj : j ≤ J) :
    sigmaSum k j (J + 1) = sigmaSum k j J + k (J + 1) :=
  Finset.sum_Ioc_succ_top hj k

theorem sigmaSum_self (k : ℕ → ℕ) (j : ℕ) : sigmaSum k j j = 0 := by
  simp [sigmaSum]

theorem sigmaSum_le (k : ℕ → ℕ) {j J : ℕ} : sigmaSum k j J ≤ sigmaSum k 0 J :=
  Finset.sum_le_sum_of_subset (Finset.Ioc_subset_Ioc (Nat.zero_le j) le_rfl)

theorem sigmaSum_congr {k k' : ℕ → ℕ} {j J : ℕ} (h : ∀ l, l ≤ J → k l = k' l) :
    sigmaSum k j J = sigmaSum k' j J := by
  unfold sigmaSum
  refine Finset.sum_congr rfl fun l hl => h l ?_
  exact (Finset.mem_Ioc.1 hl).2

theorem zero_mem_set (C : CantorData) : (0 : ℕ) ∈ C.set := ⟨0, C.enum_zero⟩

theorem dig_zero (C : CantorData) (h : ℕ) : C.Dig h 0 := ⟨0, C.zero_mem_set, by simp⟩

end CantorData

namespace CantorData

variable {X : Type*} [TopologicalSpace X] {T : X → X}

/-- The colour-focusing data up to index `J`: points `x_j` with `T^{α_j} x_j ∈ U`, colours in the
cover, and the partial sums `σ(j,j') ∈ b^h Cantor \ {0}` with the progression conditions. -/
def FocusProp (C : CantorData) (T : X → X) (U : Set X) (ns : Finset ℕ) (L h J : ℕ)
    (x : ℕ → X) (α k : ℕ → ℕ) : Prop :=
  (∀ j ≤ J, T^[α j] (x j) ∈ U) ∧ (∀ j ≤ J, α j ∈ ns) ∧
    (∀ j j', j < j' → j' ≤ J →
      C.Dig h (sigmaSum k j j') ∧ sigmaSum k j j' ≠ 0 ∧
        ∀ i, 1 ≤ i → i ≤ L → T^[α j] (T^[i * sigmaSum k j j'] (x j')) ∈ U)

/-- **Lemma `lem:color-focusing`.**  Given a finite cover of `X` by the sets `T^{-n}U` (with `n ∈ ns`)
and the progression statement of length `L` for all non-empty open sets and all digit levels, the
colour-focusing data exist for every `J`. -/
theorem color_focusing (C : CantorData) (hT : Continuous T) (hsurj : Function.Surjective T)
    {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) (ns : Finset ℕ)
    (hcov : ∀ x : X, ∃ n ∈ ns, T^[n] x ∈ U) (L h : ℕ)
    (IH : ∀ V : Set X, IsOpen V → V.Nonempty → ∀ h' : ℕ,
      ∃ y : X, ∃ r : ℕ, C.Dig h' r ∧ r ≠ 0 ∧ ∀ i < L, T^[i * r] y ∈ V) (J : ℕ) :
    ∃ (x : ℕ → X) (α k : ℕ → ℕ), FocusProp C T U ns L h J x α k := by
  induction J with
  | zero =>
    obtain ⟨u, hu⟩ := hne
    obtain ⟨α0, hα0, hα0U⟩ := hcov u
    refine ⟨fun _ => u, fun _ => α0, fun _ => 0, ?_, ?_, ?_⟩
    · intro j hj
      have : j = 0 := by omega
      subst this
      exact hα0U
    · intro j hj
      have : j = 0 := by omega
      subst this
      exact hα0
    · intro j j' hjj' hj'
      omega
  | succ J ih =>
    obtain ⟨x, α, k, hx, hα, hpairs⟩ := ih
    -- the open set of admissible points at the previous stage
    set S : ℕ := sigmaSum k 0 J with hS
    set V : Set X := ⋂ j ∈ range (J + 1), ⋂ i ∈ Finset.Icc 1 L,
      {z : X | T^[α j] (T^[i * sigmaSum k j J] z) ∈ U} with hV
    have hVopen : IsOpen V := by
      refine isOpen_biInter_finset fun j _ => isOpen_biInter_finset fun i _ => ?_
      exact (((hT.iterate (α j)).comp (hT.iterate _))).isOpen_preimage U hU
    have hVne : V.Nonempty := by
      refine ⟨x J, mem_iInter₂.2 fun j hj => mem_iInter₂.2 fun i hi => ?_⟩
      have hjJ : j ≤ J := by
        have := Finset.mem_range.1 hj
        omega
      have hi' := Finset.mem_Icc.1 hi
      rcases Nat.lt_or_eq_of_le hjJ with hlt | heq
      · exact (hpairs j J hlt le_rfl).2.2 i hi'.1 hi'.2
      · subst heq
        rw [sigmaSum_self, mul_zero, Function.iterate_zero]
        exact hx j le_rfl
    -- a progression of length `L` in `V` at a high digit level
    obtain ⟨y, r, hr, hr0, hprog⟩ := IH V hVopen hVne (h + S)
    obtain ⟨x', hx'⟩ := (hsurj.iterate r) y
    obtain ⟨α', hα'ns, hα'U⟩ := hcov x'
    refine ⟨Function.update x (J + 1) x', Function.update α (J + 1) α',
      Function.update k (J + 1) r, ?_, ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_or_eq_of_le hj with hlt | heq
      · rw [Function.update_of_ne (show j ≠ J + 1 by omega),
          Function.update_of_ne (show j ≠ J + 1 by omega)]
        exact hx j (by omega)
      · subst heq
        rw [Function.update_self, Function.update_self]
        exact hα'U
    · intro j hj
      rcases Nat.lt_or_eq_of_le hj with hlt | heq
      · rw [Function.update_of_ne (show j ≠ J + 1 by omega)]
        exact hα j (by omega)
      · subst heq
        rw [Function.update_self]
        exact hα'ns
    · intro j j' hjj' hj'
      rcases Nat.lt_or_eq_of_le hj' with hlt | heq
      · -- the pairs with both indices at most `J` are unchanged
        have e1 : sigmaSum (Function.update k (J + 1) r) j j' = sigmaSum k j j' :=
          sigmaSum_congr fun l hl => Function.update_of_ne (show l ≠ J + 1 by omega) _ _
        obtain ⟨hD, hne0, hsec⟩ := hpairs j j' hjj' (by omega)
        rw [e1, Function.update_of_ne (show j' ≠ J + 1 by omega),
          Function.update_of_ne (show j ≠ J + 1 by omega)]
        exact ⟨hD, hne0, hsec⟩
      · -- the new pairs `(j, J+1)`
        subst heq
        have hjJ : j ≤ J := by omega
        have e2 : sigmaSum (Function.update k (J + 1) r) j (J + 1) = sigmaSum k j J + r := by
          rw [sigmaSum_succ _ hjJ, Function.update_self,
            sigmaSum_congr (J := J) (k := Function.update k (J + 1) r) (k' := k) fun l hl =>
              Function.update_of_ne (show l ≠ J + 1 by omega) _ _]
        have hDa : C.Dig h (sigmaSum k j J) := by
          rcases Nat.lt_or_eq_of_le hjJ with hlt | heq
          · exact (hpairs j J hlt le_rfl).1
          · subst heq
            rw [sigmaSum_self]
            exact C.dig_zero h
        have hlt_pow : sigmaSum k j J < C.base ^ (h + S) := by
          have h1 : sigmaSum k j J ≤ S := sigmaSum_le k
          have h2 : S < C.base ^ S := Nat.lt_pow_self (by have := C.three_le_base; omega)
          have h3 : C.base ^ S ≤ C.base ^ (h + S) :=
            Nat.pow_le_pow_right (by have := C.three_le_base; omega) (Nat.le_add_left S h)
          omega
        have hDsum : C.Dig h (sigmaSum k j J + r) := by
          obtain ⟨m, hm, hmeq⟩ := C.pow_mul_add_mem_of_lt_pow (h := h) (h' := h + S)
            (c := r) (a := sigmaSum k j J) (Nat.le_add_right h S) hDa hlt_pow hr
          exact ⟨m, hm, hmeq⟩
        rw [e2]
        refine ⟨hDsum, by omega, fun i hi1 hiL => ?_⟩
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        have hzV : T^[(i' + 1) * r] x' ∈ V := by
          rw [show (i' + 1) * r = i' * r + r by ring, Function.iterate_add_apply, hx']
          exact hprog i' (by omega)
        have hmem := mem_iInter₂.1 hzV j (Finset.mem_range.2 (by omega))
        have hmem2 := mem_iInter₂.1 hmem (i' + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
        rw [Function.update_self, mul_add, Function.iterate_add_apply,
          Function.update_of_ne (show j ≠ J + 1 by omega)]
        exact hmem2

end CantorData

end CantorSzemeredi

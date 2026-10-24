/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.CondHS

/-!
# The pigeonhole step for the compact-extension argument

Blueprint: `blueprint/src/chapter/compact.tex`, Lemma `lem:unfortunate`.

Let `f` have a finite `ε/2`-net `g_1, …, g_r` for its orbit, in the sense of
`eq:net`: for every `n`, for a.e. `x`, some `g_q` is within `ε/2` of `f ∘ Tⁿ`.  If a finite
set `F` of indices has at least `r^(t+1) + 1` elements, then for a.e. `x` some pair of
distinct `a, a' ∈ F` is good at `x`: `cnorm(T^{sa} f - T^{sa'} f)(x) < ε` for `0 ≤ s ≤ t`.

The proof assigns to each `a ∈ F` the tuple of net indices chosen for `T^{sa} f`, and applies
the pigeonhole principle to these `r^(t+1) + 1` tuples.
-/

namespace CantorSzemeredi

open MeasureTheory

namespace MPS

variable {S : MPS}

/-- The conditional norm does not see a sign change. -/
theorem condNorm_neg (D : Factor S) (w : S.X → ℝ) : condNorm D (-w) = condNorm D w := by
  unfold condNorm condInner
  funext x
  simp

/-- **Lemma `lem:unfortunate`.**  Pigeonhole for good pairs. -/
theorem not_unfortunate_of_card_le (D : Factor S) {f : S.X → ℝ} (hf : MemLp f 2 S.m)
    {t r : ℕ} {g : Fin r → S.X → ℝ} (hg : ∀ q, MemLp (g q) 2 S.m) {ε : ℝ}
    (hnet : ∀ n : ℕ, ∀ᵐ x ∂S.m, ∃ q : Fin r, condNorm D (f ∘ S.T^[n] - g q) x < ε / 2)
    {F : Finset ℕ} (hF : r ^ (t + 1) + 1 ≤ F.card) :
    ∀ᵐ x ∂S.m, ∃ a ∈ F, ∃ a' ∈ F, a ≠ a' ∧
      ∀ s ≤ t, condNorm D (f ∘ S.T^[s * a] - f ∘ S.T^[s * a']) x < ε := by
  -- The triangle inequality through each fixed net element, for all countably many indices.
  have htri : ∀ᵐ x ∂S.m, ∀ s a a' : ℕ, ∀ j : Fin r,
      condNorm D (f ∘ S.T^[s * a] - f ∘ S.T^[s * a']) x
        ≤ condNorm D (f ∘ S.T^[s * a] - g j) x + condNorm D (f ∘ S.T^[s * a'] - g j) x := by
    refine ae_all_iff.2 fun s => ae_all_iff.2 fun a => ae_all_iff.2 fun a' =>
      ae_all_iff.2 fun j => ?_
    have hfa := hf.comp_measurePreserving (S.measurePreserving_T_iterate (s * a))
    have hfa' := hf.comp_measurePreserving (S.measurePreserving_T_iterate (s * a'))
    have hm1 : MemLp (f ∘ S.T^[s * a] - g j) 2 S.m := hfa.sub (hg j)
    have hm2 : MemLp (-(f ∘ S.T^[s * a'] - g j)) 2 S.m := (hfa'.sub (hg j)).neg
    have hsplit : f ∘ S.T^[s * a] - f ∘ S.T^[s * a']
        = (f ∘ S.T^[s * a] - g j) + -(f ∘ S.T^[s * a'] - g j) := by
      funext y
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
      ring
    filter_upwards [condNorm_add_le D hm1 hm2] with x hx
    rw [hsplit, ← condNorm_neg D (f ∘ S.T^[s * a'] - g j)]
    exact hx.trans (le_of_eq (by rw [condNorm_neg]))
  filter_upwards [ae_all_iff.2 hnet, htri] with x hx htx
  choose q hq using hx
  -- The tuple of net indices attached to `a ∈ F`.
  have hmaps : ∀ a ∈ F, (fun s : Fin (t + 1) => q (s * a)) ∈
      (Finset.univ : Finset (Fin (t + 1) → Fin r)) := fun a _ => Finset.mem_univ _
  have hcard : (Finset.univ : Finset (Fin (t + 1) → Fin r)).card < F.card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    omega
  obtain ⟨a, ha, a', ha', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  refine ⟨a, ha, a', ha', hne, fun s hs => ?_⟩
  have hqs : q (s * a) = q (s * a') := by
    have := congrFun heq ⟨s, Nat.lt_succ_of_le hs⟩
    simpa using this
  have h1 := hq (s * a)
  have h2 := hq (s * a')
  rw [← hqs] at h2
  have h3 := htx s a a' (q (s * a))
  linarith

end MPS

end CantorSzemeredi

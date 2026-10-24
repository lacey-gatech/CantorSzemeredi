/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.CondHS
import CantorSzemeredi.Dynamics.Localize

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

/-- `F` is *unfortunate at `x`*: no pair of distinct elements of `F` is good at `x`, where a
pair is good when `cnorm(T^{sa} f - T^{sa'} f)(x) < ε` for every `0 ≤ s ≤ t`. -/
def CondUnfortunate (D : Factor S) (f : S.X → ℝ) (t : ℕ) (ε : ℝ) (F : Finset ℕ)
    (x : S.X) : Prop :=
  ∀ a ∈ F, ∀ a' ∈ F, a ≠ a' → ∃ s ≤ t, ε ≤ condNorm D (f ∘ S.T^[s * a] - f ∘ S.T^[s * a']) x

/-- **Lemma `lem:maximal-unfortunate`.**  Almost every point is maximally unfortunate for some
finite set of indices of size below `M = r^(t+1) + 1`: `x ∈ Q(F)`. -/
theorem exists_maximal_unfortunate (D : Factor S) {f : S.X → ℝ} (hf : MemLp f 2 S.m)
    {t r : ℕ} {g : Fin r → S.X → ℝ} (hg : ∀ q, MemLp (g q) 2 S.m) {ε : ℝ}
    (hnet : ∀ n : ℕ, ∀ᵐ x ∂S.m, ∃ q : Fin r, condNorm D (f ∘ S.T^[n] - g q) x < ε / 2) :
    ∀ᵐ x ∂S.m, ∃ F : Finset ℕ, 1 ≤ F.card ∧ F.card < r ^ (t + 1) + 1 ∧
      CondUnfortunate D f t ε F x ∧
      ∀ G : Finset ℕ, F.card < G.card → ¬ CondUnfortunate D f t ε G x := by
  -- Almost surely no set of size at least `M` is unfortunate.
  have hpig : ∀ᵐ x ∂S.m, ∀ G : Finset ℕ, r ^ (t + 1) + 1 ≤ G.card →
      ∃ a ∈ G, ∃ a' ∈ G, a ≠ a' ∧ ∀ s ≤ t,
        condNorm D (f ∘ S.T^[s * a] - f ∘ S.T^[s * a']) x < ε := by
    refine ae_all_iff.2 fun G => ?_
    by_cases h : r ^ (t + 1) + 1 ≤ G.card
    · filter_upwards [not_unfortunate_of_card_le D hf hg hnet h] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall fun x hG => absurd hG h
  filter_upwards [hpig] with x hx
  have hbound : ∀ G : Finset ℕ, CondUnfortunate D f t ε G x → G.card < r ^ (t + 1) + 1 := by
    intro G hG
    by_contra hcon
    obtain ⟨a, ha, a', ha', hne, hgood⟩ := hx G (by omega)
    obtain ⟨s, hs, hle⟩ := hG a ha a' ha' hne
    exact absurd (hgood s hs) (not_lt.2 hle)
  -- The set of sizes of unfortunate sets is non-empty and bounded; its maximum is attained.
  set U : Set ℕ := {k | ∃ G : Finset ℕ, G.card = k ∧ CondUnfortunate D f t ε G x} with hU
  have h1 : 1 ∈ U := ⟨{0}, by simp, fun a ha a' ha' hne => by
    simp only [Finset.mem_singleton] at ha ha'
    exact absurd (ha.trans ha'.symm) hne⟩
  have hUbdd : BddAbove U := ⟨r ^ (t + 1), fun k ⟨G, hk, hG⟩ => by
    rw [← hk]; exact Nat.lt_succ_iff.1 (hbound G hG)⟩
  obtain ⟨F, hFcard, hF⟩ := Nat.sSup_mem ⟨1, h1⟩ hUbdd
  refine ⟨F, ?_, ?_, hF, ?_⟩
  · have := le_csSup hUbdd h1
    omega
  · have := hbound F hF
    omega
  · intro G hG hcon
    have hmem : G.card ∈ U := ⟨G, rfl, hcon⟩
    have := le_csSup hUbdd hmem
    omega

/-- **Lemma `lem:return-time`.**  Let `E` lie in the set `Q(F)` of maximally unfortunate points,
and let `q` assign to each ordered pair `(a, a')` of `F` an exponent `q a a' ≤ t` at which the
pair is bad on `E`.  If `n` exceeds every element of `F`, then for almost every `x` with
`T^{sn} x ∈ E` for `0 ≤ s ≤ t`, some `a ∈ F` makes `T^{s(n+a)} f` close to `f` for all `s ≤ t`. -/
theorem exists_good_translate (D : Factor S) {f : S.X → ℝ} (hf : MemLp f 2 S.m)
    {t : ℕ} {ε : ℝ} {F : Finset ℕ} {E : Set S.X} {q : ℕ → ℕ → ℕ}
    (hqt : ∀ a a', q a a' ≤ t)
    (hE : ∀ y ∈ E, ∀ a ∈ F, ∀ a' ∈ F, a ≠ a' →
      ε ≤ condNorm D (f ∘ S.T^[q a a' * a] - f ∘ S.T^[q a a' * a']) y)
    (hEQ : ∀ y ∈ E, ∀ G : Finset ℕ, F.card < G.card → ¬ CondUnfortunate D f t ε G y)
    {n : ℕ} (hFn : ∀ a ∈ F, a < n) :
    ∀ᵐ x ∂S.m, x ∈ E → (∀ s ≤ t, S.T^[s * n] x ∈ E) →
      ∃ a ∈ F, ∀ s ≤ t, condNorm D (f ∘ S.T^[s * (n + a)] - f) x < ε := by
  -- Equivariance of the conditional norm under the shift `T^{s0 n}`, for all indices at once.
  have hcomm : ∀ᵐ x ∂S.m, ∀ s0 a a' : ℕ,
      condNorm D (f ∘ S.T^[s0 * (n + a)] - f ∘ S.T^[s0 * (n + a')]) x
        = condNorm D (f ∘ S.T^[s0 * a] - f ∘ S.T^[s0 * a']) (S.T^[s0 * n] x) := by
    refine ae_all_iff.2 fun s0 => ae_all_iff.2 fun a => ae_all_iff.2 fun a' => ?_
    have hv : MemLp (f ∘ S.T^[s0 * a] - f ∘ S.T^[s0 * a']) 2 S.m :=
      ((hf.comp_measurePreserving (S.measurePreserving_T_iterate (s0 * a))).sub
        (hf.comp_measurePreserving (S.measurePreserving_T_iterate (s0 * a'))))
    have hfun : f ∘ S.T^[s0 * (n + a)] - f ∘ S.T^[s0 * (n + a')]
        = (f ∘ S.T^[s0 * a] - f ∘ S.T^[s0 * a']) ∘ S.T^[s0 * n] := by
      funext y
      simp only [Pi.sub_apply, Function.comp_apply]
      rw [show s0 * (n + a) = s0 * a + s0 * n by ring,
        show s0 * (n + a') = s0 * a' + s0 * n by ring,
        Function.iterate_add_apply, Function.iterate_add_apply]
    rw [hfun]
    filter_upwards [condNorm_comp_iterate D (s0 * n) hv] with x hx
    exact hx
  filter_upwards [hcomm] with x hcx hxE hTE
  -- The finite set `G = {0} ∪ (n + F)`, of size `|F| + 1`, is not unfortunate at `x`.
  have hzero : (0 : ℕ) ∉ F.image (fun b => n + b) := by
    intro h
    obtain ⟨b, hb, hbn⟩ := Finset.mem_image.1 h
    have := hFn b hb
    omega
  have hcardG : (insert 0 (F.image (fun b => n + b))).card = F.card + 1 := by
    rw [Finset.card_insert_of_notMem hzero, Finset.card_image_of_injective _
      (add_right_injective n)]
  have hG := hEQ x hxE (insert 0 (F.image (fun b => n + b))) (by omega)
  unfold CondUnfortunate at hG
  push Not at hG
  obtain ⟨a, ha, a', ha', hne, hlt⟩ := hG
  simp only [Finset.mem_insert, Finset.mem_image] at ha ha'
  rcases ha with rfl | ⟨b, hb, rfl⟩ <;> rcases ha' with rfl | ⟨b', hb', rfl⟩
  · exact absurd rfl hne
  · refine ⟨b', hb', fun s hs => ?_⟩
    have := hlt s hs
    rw [← condNorm_neg] at this
    convert this using 2
    simp
  · refine ⟨b, hb, fun s hs => ?_⟩
    simpa using hlt s hs
  · -- Both elements are translates: the pair `(b, b')` is bad on `E`.
    have hbb : b ≠ b' := fun h => hne (by rw [h])
    have hs0 := hqt b b'
    have hy := hTE (q b b') hs0
    have hgood := hE _ hy b hb b' hb' hbb
    have hl := hlt (q b b') hs0
    rw [hcx (q b b') b b'] at hl
    linarith

end MPS

end CantorSzemeredi

/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.WMClass

/-!
# The a.e. transfer for the re-indexed estimate

Blueprint: `blueprint/src/chapter/weakmixing.tex`, `lem:wm-main`, Step 1.  The induction
hypothesis is applied to clipped conditional expectations of the re-indexed factors on the
power system `S.pow (b^ℓ)`.  This file shows that, almost everywhere, these clipped
expectations are the blueprint's `Exp(F_j | D)` composed with the shifts `T^{(s_j - s_0) k_n}`,
so that the induction hypothesis is a statement about the blueprint's `W_n`.
-/

namespace CantorSzemeredi

open MeasureTheory Finset Filter Topology

namespace MPS

/-- Iterates of the power system: `(S.pow m)`-shifts are `S`-shifts by `m · p`. -/
theorem pow_iterate_eq (S : MPS) (m p : ℕ) (x : S.X) :
    (S.pow m).T^[p] x = S.T^[m * p] x := by
  rw [Function.iterate_mul]
  rfl


/-- **The a.e. identity, one factor.**  At the block index `a`, the clipped conditional expectation
of the re-indexed factor `F_{i+1} ∘ T^{e k_c}` on the power system, evaluated at the block
point, equals the blueprint's `Exp(F_{i+1} | D)` at the point `T^{e k_n}x`, `n = q a + c`,
almost everywhere. -/
theorem ae_clip_block {S : MPS.{0}} (C : CantorData) (s : ℕ → ℕ) (t ℓ c a : ℕ)
    (hc : c < C.delta ^ ℓ) (hs : GoodExp s (t + 1)) (D : Factor S) (F : ℕ → S.X → ℝ) (K : ℝ)
    (hK0 : 0 ≤ K) (hFm : ∀ j, j < t + 1 → Measurable (F j))
    (hFb : ∀ j, j < t + 1 → ∀ x, |F j x| ≤ K) (i : ℕ) (hi : i < t) :
    ∀ᵐ x ∂S.m,
      max (-K) (min K (S.m[fun y => F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum c] y) | D.σ]
          ((S.pow (C.base ^ ℓ)).T^[(s (i + 1) - s 0) * C.enum a] x)))
        = (S.m[F (i + 1) | D.σ]) (S.T^[(s (i + 1) - s 0) * C.enum (C.delta ^ ℓ * a + c)] x) := by
  set e := s (i + 1) - s 0 with he
  set n := e * C.enum c with hn
  have hGm : Measurable (fun y => F (i + 1) (S.T^[n] y)) := (hFm (i + 1) (by omega)).comp
    (S.measurable_T.iterate n)
  have hGb : ∀ y, |F (i + 1) (S.T^[n] y)| ≤ K := fun y => hFb (i + 1) (by omega) _
  have hint : Integrable (fun y => F (i + 1) (S.T^[n] y)) S.m :=
    integrable_of_bdd_const hGm hGb
  have hmemG : MemLp (fun y => F (i + 1) (S.T^[n] y)) 2 S.m :=
    MemLp.of_bound hGm.aestronglyMeasurable K (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hGb y)
  have hFint : Integrable (F (i + 1)) S.m := integrable_of_bdd_const (hFm (i + 1) (by omega))
    (fun y => hFb (i + 1) (by omega) y)
  have hFmem : MemLp (F (i + 1)) 2 S.m :=
    MemLp.of_bound (hFm (i + 1) (by omega)).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hFb (i + 1) (by omega) y)
  -- the clipping is an a.e. identity for the conditional expectation of the shifted factor
  have hclip := clip_ae_eq (condExp_facts D hint hGb hmemG 0).1
  -- and the conditional expectation of a composition is the composition of the expectation
  have hcomp : S.m[fun y => F (i + 1) (S.T^[n] y) | D.σ] =ᵐ[S.m]
      (S.m[F (i + 1) | D.σ]) ∘ S.T^[n] :=
    (condExp_facts D hFint (hFb (i + 1) (by omega)) hFmem n).2.2.1
  have hcomb : ∀ᵐ y ∂S.m, max (-K) (min K (S.m[fun y => F (i + 1) (S.T^[n] y) | D.σ] y))
      = (S.m[F (i + 1) | D.σ]) (S.T^[n] y) := by
    filter_upwards [hclip, hcomp] with y h1 h2
    rw [h1, h2]
    rfl
  have hpull := (S.measurePreserving_T_iterate (C.base ^ ℓ * (e * C.enum a))).quasiMeasurePreserving.ae
    hcomb
  have hidx : ∀ x, S.T^[n] (S.T^[C.base ^ ℓ * (e * C.enum a)] x)
      = S.T^[e * C.enum (C.delta ^ ℓ * a + c)] x := by
    intro x
    rw [← pow_iterate_eq S (C.base ^ ℓ) (e * C.enum a) x, hn, C.enum_block ℓ a hc,
      iterate_block_comm]
  filter_upwards [hpull] with x hx
  rw [pow_iterate_eq S (C.base ^ ℓ) (e * C.enum a) x, ← hidx x]
  exact hx

/-- **The a.e. identity, the product of the factors.**  For `n = q a + c`, the product of the
clipped expectations on the power system equals the product of the `Exp(F_{i+1} | D)` at the
points `T^{e_i k_n} x`, almost everywhere. -/
theorem ae_prod_block {S : MPS.{0}} (C : CantorData) (s : ℕ → ℕ) (t ℓ c a : ℕ)
    (hc : c < C.delta ^ ℓ) (hs : GoodExp s (t + 1)) (D : Factor S) (F : ℕ → S.X → ℝ) (K : ℝ)
    (hK0 : 0 ≤ K) (hFm : ∀ j, j < t + 1 → Measurable (F j))
    (hFb : ∀ j, j < t + 1 → ∀ x, |F j x| ≤ K) :
    ∀ᵐ x ∂S.m,
      ∏ i ∈ range t, max (-K) (min K (S.m[fun y => F (i + 1) (S.T^[(s (i + 1) - s 0)
          * C.enum c] y) | D.σ] ((S.pow (C.base ^ ℓ)).T^[(s (i + 1) - s 0) * C.enum a] x)))
        = ∏ i ∈ range t, (S.m[F (i + 1) | D.σ])
            (S.T^[(s (i + 1) - s 0) * C.enum (C.delta ^ ℓ * a + c)] x) := by
  have h := (Filter.eventually_all_finset (range t)).2 fun i hi =>
    ae_clip_block C s t ℓ c a hc hs D F K hK0 hFm hFb i (mem_range.1 hi)
  filter_upwards [h] with x hx
  exact Finset.prod_congr rfl fun i hi => hx i hi

/-- The re-indexed shift lands on the class point: `T^{e k_c}` after the block shift
`T^{m e k_a}` is the shift `T^{e k_{q a + c}}`. -/
theorem shift_block_eq (C : CantorData) (ℓ c a e : ℕ) (hc : c < C.delta ^ ℓ) {S : MPS.{0}}
    (x : S.X) :
    S.T^[e * C.enum c] ((S.pow (C.base ^ ℓ)).T^[e * C.enum a] x)
      = S.T^[e * C.enum (C.delta ^ ℓ * a + c)] x := by
  rw [C.enum_block ℓ a hc, iterate_block_comm]

/-- **The a.e. identity, one block index.**  The difference of the re-indexed products at the
block index `a` equals the blueprint's `W_{q a + c}` almost everywhere. -/
theorem ae_diff_block {S : MPS.{0}} (C : CantorData) (s : ℕ → ℕ) (t ℓ c a : ℕ)
    (hc : c < C.delta ^ ℓ) (hs : GoodExp s (t + 1)) (D : Factor S) (F : ℕ → S.X → ℝ) (K : ℝ)
    (hK0 : 0 ≤ K) (hFm : ∀ j, j < t + 1 → Measurable (F j))
    (hFb : ∀ j, j < t + 1 → ∀ x, |F j x| ≤ K) :
    ∀ᵐ x ∂S.m,
      (∏ i ∈ range t, F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum c]
          ((S.pow (C.base ^ ℓ)).T^[(s (i + 1) - s 0) * C.enum a] x)))
        - ∏ i ∈ range t, max (-K) (min K (S.m[fun y => F (i + 1) (S.T^[(s (i + 1) - s 0)
            * C.enum c] y) | D.σ] ((S.pow (C.base ^ ℓ)).T^[(s (i + 1) - s 0) * C.enum a] x)))
      = (∏ i ∈ range t, F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum (C.delta ^ ℓ * a + c)] x))
        - ∏ i ∈ range t, (S.m[F (i + 1) | D.σ])
            (S.T^[(s (i + 1) - s 0) * C.enum (C.delta ^ ℓ * a + c)] x) := by
  filter_upwards [ae_prod_block C s t ℓ c a hc hs D F K hK0 hFm hFb] with x hx
  rw [hx]
  congr 1
  exact Finset.prod_congr rfl fun i _ =>
    congrArg (F (i + 1)) (shift_block_eq (S := S) C ℓ c a _ hc x)

/-- **Step 1, the class averages of the blueprint's `W_n`.**  Under the difference form at `t`
for the induction, the averages of `W_n = ∏ F_{i+1}∘T^{e_i k_n} - ∏ Exp(F_{i+1}|D)∘T^{e_i k_n}`
over the residue class `n ≡ c mod δ^ℓ` tend to zero along the uniform filter. -/
theorem tendsto_wClass (C : CantorData) (t : ℕ) (hIH : DiffForm C t) (S : MPS.{0})
    (s : ℕ → ℕ) (hs : GoodExp s (t + 1)) (D E : Factor S) (hDE : D.σ ≤ E.σ)
    (hWM : S.WMHyp D E) (ℓ c : ℕ) (hc : c < C.delta ^ ℓ) (F : ℕ → S.X → ℝ) (K : ℝ)
    (hK0 : 0 ≤ K) (hFm : ∀ j, j < t + 1 → Measurable[E.σ] (F j))
    (hFb : ∀ j, j < t + 1 → ∀ x, |F j x| ≤ K) :
    Tendsto (fun p : ℕ × ℕ => eLpNorm
        (fun x => (((Ico p.1 p.2).filter (fun n => n % C.delta ^ ℓ = c)).card : ℝ)⁻¹
          * ∑ n ∈ (Ico p.1 p.2).filter (fun n => n % C.delta ^ ℓ = c),
              (∏ i ∈ range t, F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum n] x)
                - ∏ i ∈ range t, (S.m[F (i + 1) | D.σ]) (S.T^[(s (i + 1) - s 0) * C.enum n] x)))
        2 S.m) uniformFilter (𝓝 0) := by
  have hq : 0 < C.delta ^ ℓ := Nat.pow_pos (by have := C.two_le_delta; omega)
  have hm : 1 ≤ C.base ^ ℓ := Nat.one_le_pow ℓ C.base (by have := C.three_le_base; omega)
  have hFm' : ∀ j, j < t + 1 → Measurable (F j) := fun j hj => (hFm j hj).mono E.le le_rfl
  have hR := reindexed_diff C t hIH S s hs D E hDE hWM (C.base ^ ℓ) hm c F K hK0 hFm hFb
  refine tendsto_classAvg (μ := S.m) hq hc
    (fun n x => ∏ i ∈ range t, F (i + 1) (S.T^[(s (i + 1) - s 0) * C.enum n] x)
      - ∏ i ∈ range t, (S.m[F (i + 1) | D.σ]) (S.T^[(s (i + 1) - s 0) * C.enum n] x)) ?_
  refine Tendsto.congr' (Filter.Eventually.of_forall fun p => ?_) hR
  apply eLpNorm_congr_ae
  filter_upwards [(Filter.eventually_all_finset (Ico p.1 p.2)).2 fun a _ =>
    ae_diff_block C s t ℓ c a hc hs D F K hK0 hFm' hFb] with x hx
  simp only [avgProd, Pi.sub_apply]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  exact congrArg (fun y => ((p.2 - p.1 : ℕ) : ℝ)⁻¹ * y) (Finset.sum_congr rfl fun a ha => hx a ha)

end MPS

end CantorSzemeredi

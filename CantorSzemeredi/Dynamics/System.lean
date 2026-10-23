/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Basic

/-!
# Invertible measure preserving systems and their factors

Stage 3 of the blueprint (`blueprint/src/chapter/mps.tex`).  This file sets up the objects the
rest of the development quantifies over.

## Design

`MPS` bundles `(X, 𝒜, m, T)` with `T` an invertible measure preserving map.  The blueprint asks
for a bundle rather than a sea of hypotheses because the development quantifies over systems
(Zorn's lemma over the CSZ factors), over powers `T^k` of a single system, and over the product
system on `X × X` used for the relatively independent self-joining.

A `Factor` is a `T`-invariant sub-σ-algebra.  Invariance is stated as the *equivalence*
`MeasurableSet[D] (T ⁻¹' s) ↔ MeasurableSet[D] s`, not merely the forward implication.  For an
invertible system this is the right notion, and it is exactly what `condExp_comp` below needs:
pushing a `D`-set forward along `T` must land in `D` again.
-/

namespace CantorSzemeredi

open MeasureTheory Filter

/-- An invertible measure preserving system `(X, 𝒜, m, T)`. -/
structure MPS where
  /-- The underlying space. -/
  X : Type*
  /-- The ambient σ-algebra `𝒜`. -/
  [measurableSpace : MeasurableSpace X]
  /-- The invariant probability measure. -/
  m : Measure X
  /-- The measure is a probability measure. -/
  [isProb : IsProbabilityMeasure m]
  /-- The transformation. -/
  T : X → X
  /-- `T` is a measurable equivalence of `X` with itself. -/
  measurableEquiv : X ≃ᵐ X
  /-- The equivalence is `T`. -/
  coe_measurableEquiv : ⇑measurableEquiv = T
  /-- `T` preserves `m`. -/
  measurePreserving : MeasurePreserving T m m

attribute [instance] MPS.measurableSpace MPS.isProb

namespace MPS

variable (S : MPS)

instance : MeasurableSpace S.X := S.measurableSpace

theorem measurable_T : Measurable S.T := S.measurePreserving.measurable

/-- The inverse of `T`. -/
def Tinv : S.X → S.X := S.measurableEquiv.symm

theorem measurable_Tinv : Measurable S.Tinv := S.measurableEquiv.symm.measurable

@[simp] theorem Tinv_T (x : S.X) : S.Tinv (S.T x) = x := by
  simp [Tinv, ← S.coe_measurableEquiv]

@[simp] theorem T_Tinv (x : S.X) : S.T (S.Tinv x) = x := by
  simp [Tinv, ← S.coe_measurableEquiv]

theorem preimage_T_image (s : Set S.X) : S.T ⁻¹' (S.T '' s) = s := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := by
      have := congrArg S.Tinv hxy
      simpa using this
    exact this ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

/-- `T⁻¹` preserves the measure too. -/
theorem measurePreserving_Tinv (S : MPS) : MeasurePreserving S.Tinv S.m S.m := by
  refine ⟨S.measurable_Tinv, ?_⟩
  have hmap := S.measurePreserving.map_eq
  calc Measure.map S.Tinv S.m
      = Measure.map S.Tinv (Measure.map S.T S.m) := by rw [hmap]
    _ = Measure.map (S.Tinv ∘ S.T) S.m :=
        Measure.map_map S.measurable_Tinv S.measurable_T
    _ = S.m := by simp [Function.comp_def]

/-- `T` is a measure preserving *equivalence*, so `m (T '' s) = m s` for measurable `s`. -/
theorem measure_image_T {s : Set S.X} (hs : MeasurableSet s) : S.m (S.T '' s) = S.m s := by
  have himg : S.T '' s = S.Tinv ⁻¹' s := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · exact fun hx => ⟨S.Tinv x, hx, by simp⟩
  rw [himg]
  have : MeasurePreserving S.Tinv S.m S.m := S.measurePreserving_Tinv
  rw [← this.measure_preimage hs.nullMeasurableSet]

/-! ### The `ℤ`-indexed orbit

`T` is invertible, so the orbit of a point is indexed by `ℤ`.  The conditional compactness of
`def:compact-extension` takes a supremum over `n ∈ ℤ`, so this is needed to state it. -/

/-- `S.iter n` is `T^n` for `n : ℤ`, using `T⁻¹` for negative `n`. -/
noncomputable def iter (S : MPS) : ℤ → S.X → S.X
  | Int.ofNat n => S.T^[n]
  | Int.negSucc n => S.Tinv^[n + 1]

@[simp] theorem iter_natCast (S : MPS) (n : ℕ) : S.iter n = S.T^[n] := rfl

@[simp] theorem iter_zero (S : MPS) : S.iter 0 = id := rfl

theorem measurable_iter (S : MPS) (n : ℤ) : Measurable (S.iter n) := by
  cases n with
  | ofNat n => exact S.measurable_T.iterate n
  | negSucc n => exact S.measurable_Tinv.iterate (n + 1)

theorem measurePreserving_T_iterate (S : MPS) (n : ℕ) :
    MeasurePreserving S.T^[n] S.m S.m := by
  induction n with
  | zero => simpa using MeasurePreserving.id S.m
  | succ n ih => rw [Function.iterate_succ]; exact ih.comp S.measurePreserving

/-! ### Powers of a system

The development repeatedly replaces `T` by `T^k`: the compact extension argument runs at
`T^(b^i)` (`rem:compact-dilation`), and the weakly mixing induction applies its hypothesis to
`T^(b^ℓ)`.  `S.pow k` is the same space and measure with `T` replaced by `T^k`. -/

/-- The measurable equivalence `T^k`. -/
noncomputable def equivPow (S : MPS) : ℕ → (S.X ≃ᵐ S.X)
  | 0 => MeasurableEquiv.refl S.X
  | k + 1 => (S.equivPow k).trans S.measurableEquiv

theorem coe_equivPow (S : MPS) (k : ℕ) : ⇑(S.equivPow k) = S.T^[k] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x
    simp only [equivPow, MeasurableEquiv.coe_trans, Function.comp_apply, ih,
      S.coe_measurableEquiv]
    rw [← Function.iterate_succ_apply' S.T k]

/-- `S.pow k` is the system `(X, 𝒜, m, T^k)`. -/
noncomputable def pow (S : MPS) (k : ℕ) : MPS where
  X := S.X
  measurableSpace := S.measurableSpace
  m := S.m
  isProb := S.isProb
  T := S.T^[k]
  measurableEquiv := S.equivPow k
  coe_measurableEquiv := S.coe_equivPow k
  measurePreserving := S.measurePreserving_T_iterate k

@[simp] theorem pow_X (S : MPS) (k : ℕ) : (S.pow k).X = S.X := rfl

@[simp] theorem pow_m (S : MPS) (k : ℕ) : (S.pow k).m = S.m := rfl

@[simp] theorem pow_T (S : MPS) (k : ℕ) : (S.pow k).T = S.T^[k] := rfl

theorem leftInverse_Tinv (S : MPS) : Function.LeftInverse S.Tinv S.T := S.Tinv_T

theorem rightInverse_Tinv (S : MPS) : Function.RightInverse S.Tinv S.T := S.T_Tinv

@[simp] theorem pow_Tinv (S : MPS) (k : ℕ) : (S.pow k).Tinv = S.Tinv^[k] := by
  funext x
  have hleft : Function.LeftInverse S.Tinv^[k] S.T^[k] := S.leftInverse_Tinv.iterate k
  have hcoe : ⇑(S.equivPow k) = S.T^[k] := S.coe_equivPow k
  have hinj : Function.Injective (S.T^[k]) := by
    rw [← hcoe]
    exact (S.equivPow k).injective
  refine hinj ?_
  have h₁ : S.T^[k] ((S.pow k).Tinv x) = x := (S.pow k).T_Tinv x
  have h₂ : S.T^[k] (S.Tinv^[k] x) = x := S.rightInverse_Tinv.iterate k x
  rw [h₁, h₂]

/-- `S.iter` at a negative integer is an iterate of `T⁻¹`. -/
theorem iter_neg_natCast (S : MPS) (j : ℕ) : S.iter (-(j : ℤ)) = S.Tinv^[j] := by
  cases j with
  | zero => rfl
  | succ j =>
    have hneg : -((j + 1 : ℕ) : ℤ) = Int.negSucc j := by
      simp [Int.negSucc_eq]
    rw [hneg]
    rfl

/-- The `ℤ`-orbit of `S.pow k` sits inside the `ℤ`-orbit of `S`: `(T^k)^n = T^(k n)`. -/
theorem pow_iter_eq (S : MPS) (k : ℕ) (n : ℤ) : (S.pow k).iter n = S.iter (k * n) := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, iter_natCast, pow_T]
    rw [show ((k : ℤ) * (n : ℤ)) = ((k * n : ℕ) : ℤ) by push_cast; ring, iter_natCast,
      Function.iterate_mul]
    rfl
  | negSucc n =>
    have hlhs : (S.pow k).iter (Int.negSucc n) = S.Tinv^[k * (n + 1)] := by
      change (S.pow k).Tinv^[n + 1] = _
      rw [S.pow_Tinv k]
      exact (Function.iterate_mul S.Tinv k (n + 1)).symm
    have hmul : (k : ℤ) * Int.negSucc n = -((k * (n + 1) : ℕ) : ℤ) := by
      simp only [Int.negSucc_eq]
      push_cast
      ring
    rw [hlhs, hmul, S.iter_neg_natCast]

/-! ### Factors -/

/-- **Definition `def:factor`.**  A *factor* of `S` is a `T`-invariant sub-σ-algebra of `𝒜`.

Invariance is the equivalence `MeasurableSet[D] (T ⁻¹' s) ↔ MeasurableSet[D] s`, not just the
forward implication: for an invertible system that is the right notion, and it is what
`condExp_comp` needs, since that proof pushes a `D`-set forward along `T`. -/
structure Factor (S : MPS) where
  /-- The sub-σ-algebra. -/
  σ : MeasurableSpace S.X
  /-- It is contained in the ambient σ-algebra. -/
  le : σ ≤ S.measurableSpace
  /-- It is `T`-invariant. -/
  invariant : ∀ s : Set S.X, MeasurableSet[σ] (S.T ⁻¹' s) ↔ MeasurableSet[σ] s

namespace Factor

variable {S : MPS} (D : Factor S)

instance : CoeSort (Factor S) (MeasurableSpace S.X) := ⟨Factor.σ⟩

/-- A `D`-measurable set stays `D`-measurable under `T ⁻¹`. -/
theorem measurableSet_preimage {s : Set S.X} (hs : MeasurableSet[D.σ] s) :
    MeasurableSet[D.σ] (S.T ⁻¹' s) := (D.invariant s).2 hs

/-- A `D`-measurable set stays `D`-measurable under the forward image. -/
theorem measurableSet_image {s : Set S.X} (hs : MeasurableSet[D.σ] s) :
    MeasurableSet[D.σ] (S.T '' s) :=
  (D.invariant (S.T '' s)).1 (by rwa [S.preimage_T_image])

instance : SigmaFinite (S.m.trim D.le) := by
  have : IsProbabilityMeasure (S.m.trim D.le) :=
    ⟨by rw [trim_measurableSet_eq D.le MeasurableSet.univ, measure_univ]⟩
  infer_instance

/-- `T ⁻¹' s` determines `s`, since `T` is a bijection. -/
theorem preimage_eq_empty_iff (S : MPS) {s : Set S.X} : S.T ⁻¹' s = ∅ ↔ s = ∅ := by
  constructor
  · intro h
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have : S.Tinv x ∈ S.T ⁻¹' s := by simpa using hx
    rw [h] at this
    exact this
  · rintro rfl
    simp

theorem preimage_eq_univ_iff (S : MPS) {s : Set S.X} : S.T ⁻¹' s = Set.univ ↔ s = Set.univ := by
  constructor
  · intro h
    ext x
    simp only [Set.mem_univ, iff_true]
    have : S.Tinv x ∈ S.T ⁻¹' s := by rw [h]; trivial
    simpa using this
  · rintro rfl
    simp

/-- The trivial factor: the null and conull sets, i.e. `⊥`. -/
def trivial (S : MPS) : Factor S where
  σ := ⊥
  le := bot_le
  invariant s := by
    simp only [MeasurableSpace.measurableSet_bot_iff]
    rw [preimage_eq_empty_iff, preimage_eq_univ_iff]

/-! ### Conditional expectation and the dynamics

The one fact about `condExp` that the whole development rests on: on a `T`-invariant
σ-algebra, conditional expectation commutes with the Koopman operator.  Mathlib has no lemma
relating `condExp` to a measure preserving map, so this is proved from the characterization of
`condExp` by its integrals over `D`-measurable sets.
-/

/-- **Lemma `lem:condexp-commutes`.**  `E(a ∘ T | D) = E(a | D) ∘ T` almost everywhere, for a
`T`-invariant factor `D`. -/
theorem condExp_comp (D : Factor S) {a : S.X → ℝ} (ha : Integrable a S.m) :
    (S.m[a|D.σ]) ∘ S.T =ᵐ[S.m] S.m[a ∘ S.T|D.σ] := by
  have hTm : MeasurePreserving S.T S.m S.m := S.measurePreserving
  have hcomp_int : Integrable (a ∘ S.T) S.m := (hTm.integrable_comp ha.aestronglyMeasurable).2 ha
  -- `E(a|D) ∘ T` is `D`-measurable, because `T` is `D`-`D` measurable.
  have hTD : @Measurable S.X S.X D.σ D.σ S.T := fun s hs => D.measurableSet_preimage hs
  have hmeas : StronglyMeasurable[D.σ] ((S.m[a|D.σ]) ∘ S.T) :=
    (stronglyMeasurable_condExp (m := D.σ)).comp_measurable hTD
  have hint : Integrable ((S.m[a|D.σ]) ∘ S.T) S.m :=
    (hTm.integrable_comp (integrable_condExp.aestronglyMeasurable)).2 integrable_condExp
  refine ae_eq_condExp_of_forall_setIntegral_eq D.le hcomp_int ?_ ?_ hmeas.aestronglyMeasurable
  · intro s hs _
    exact hint.integrableOn
  · intro s hs hfin
    -- Push `s` forward along `T`; it is again `D`-measurable, and `T` preserves `m`.
    have hsA : MeasurableSet s := D.le s hs
    have himg : MeasurableSet[D.σ] (S.T '' s) := D.measurableSet_image hs
    have himgA : MeasurableSet (S.T '' s) := D.le _ himg
    have hpre : S.T ⁻¹' (S.T '' s) = s := S.preimage_T_image s
    have hemb : MeasurableEmbedding S.T := by
      rw [← S.coe_measurableEquiv]
      exact S.measurableEquiv.measurableEmbedding
    have key : ∀ g : S.X → ℝ,
        ∫ x in s, g (S.T x) ∂S.m = ∫ x in S.T '' s, g x ∂S.m := by
      intro g
      have h := hTm.setIntegral_preimage_emb hemb g (S.T '' s)
      rw [hpre] at h
      exact h
    change ∫ x in s, (S.m[a|D.σ]) (S.T x) ∂S.m = ∫ x in s, a (S.T x) ∂S.m
    rw [key a, key (S.m[a|D.σ]), setIntegral_condExp D.le ha himg]

end Factor

end MPS

end CantorSzemeredi

/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.HilbertModule

/-!
# Weakly mixing and compact extensions

Blueprint: `def:weak-mixing`, `def:compact-system`, `def:cwm` and `def:compact-extension` in
`blueprint/src/chapter/mps.tex`.

## A warning carried over from the blueprint

These are Moreira's definitions **except** that conditional weak mixing is asked only for
`g = f`, and with ordinary Cesàro means rather than uniform ones.  That is a *weaker*
requirement on `f`, hence a *weaker* hypothesis on the extension — which is the direction that
makes the dichotomy (`lem:dichotomy`) apply as stated: a weakly mixing extension in Moreira's
sense is one in ours.  If this asymmetry is reproduced backwards, the dichotomy will not fit
the extension principles.  `CondWeaklyMixing` below is therefore deliberately the `g = f`,
ordinary-Cesàro version, and must not be "improved".

## `L²(D)` norms

A conditional inner product is `D`-measurable, and the measure on `D` is the restriction of
`m`, so its `L²(D)` norm is just its `L²(m)` norm.  We use `eLpNorm _ 2 S.m` throughout rather
than introducing a separate `L²(D)` space.
-/

namespace CantorSzemeredi

open MeasureTheory Filter Topology

namespace MPS

variable {S : MPS}

/-- Membership in the Hilbert module `L²(E|D)`: `E`-measurable, square integrable, and with
conditional norm essentially bounded. -/
structure MemModule (D E : Factor S) (f : S.X → ℝ) : Prop where
  /-- `f` is `E`-measurable. -/
  meas : AEStronglyMeasurable[E.σ] f S.m
  /-- `f` is square integrable. -/
  memLp : MemLp f 2 S.m
  /-- The conditional norm of `f` is essentially bounded. -/
  bddCondNorm : ∃ C : ℝ, ∀ᵐ x ∂S.m, condNorm D f x ≤ C

/-- **Definition `def:cwm`.**  `f` is *conditionally weakly mixing* if the Cesàro averages of
`|⟨T^n f, f⟩_{E|D}|` tend to `0` in `L²(D)`.

Deliberately the `g = f`, ordinary-Cesàro version; see the module docstring. -/
def CondWeaklyMixing (D : Factor S) (f : S.X → ℝ) : Prop :=
  Tendsto (fun N : ℕ => eLpNorm
      (fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, |condInner D (f ∘ S.T^[n]) f x|) 2 S.m)
    atTop (𝓝 0)

/-- **Definition `def:cwm`.**  `E | D` is a *weakly mixing extension* if every `f` in the
Hilbert module with `E(f|D) = 0` is conditionally weakly mixing. -/
def WeaklyMixingExtension (D E : Factor S) : Prop :=
  ∀ f : S.X → ℝ, MemModule D E f → (S.m[f|D.σ]) =ᵐ[S.m] 0 → CondWeaklyMixing D f

/-- **Definition `def:compact-extension`.**  `f` is *conditionally compact* if its `ℤ`-orbit is
covered, to within `ε` in the conditional sup norm, by finitely many module elements. -/
def CondCompact (D E : Factor S) (f : S.X → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (r : ℕ) (g : Fin r → S.X → ℝ), (∀ q, MemModule D E (g q)) ∧
    ∀ n : ℤ, ∃ q : Fin r, ∀ᵐ x ∂S.m, condNorm D (f ∘ S.iter n - g q) x < ε

/-- **Definition `def:compact-extension`.**  `E | D` is a *compact extension* if the
conditionally compact functions are dense in `L²(E)`. -/
def CompactExtension (D E : Factor S) : Prop :=
  ∀ f : S.X → ℝ, AEStronglyMeasurable[E.σ] f S.m → MemLp f 2 S.m → ∀ ε : ℝ, 0 < ε →
    ∃ g : S.X → ℝ, CondCompact D E g ∧ eLpNorm (f - g) 2 S.m ≤ ENNReal.ofReal ε

/-- **Definition `def:weak-mixing`.**  The system is weakly mixing. -/
def WeaklyMixing (S : MPS) : Prop :=
  ∀ A B : Set S.X, MeasurableSet A → MeasurableSet B →
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        |(S.m (A ∩ S.T^[n] ⁻¹' B)).toReal - (S.m A).toReal * (S.m B).toReal|)
      atTop (𝓝 0)

/-- **Definition `def:compact-system`.**  `f` is *compact* if its `ℤ`-orbit is totally bounded
in `L²`, which in the complete space `L²` is precompactness of the orbit closure.

Stated as total boundedness rather than `IsCompact (closure ...)` to avoid coercing the orbit
into `Lp`; this is also the form in which compactness is used.  Note that compact *systems*
play no role in the proof of the main theorem — only compact *extensions* do. -/
def CompactFunction (S : MPS) (f : S.X → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (r : ℕ) (g : Fin r → S.X → ℝ),
    ∀ n : ℤ, ∃ q : Fin r, eLpNorm (f ∘ S.iter n - g q) 2 S.m ≤ ENNReal.ofReal ε

/-- The system is *compact* if every square integrable `f` is. -/
def CompactSystem (S : MPS) : Prop :=
  ∀ f : S.X → ℝ, MemLp f 2 S.m → S.CompactFunction f

/-! ### Passing to powers

`lem:powers`(1): a compact extension for `T` is one for `T^k`.  The orbit of `T^k` is a subset
of the orbit of `T` (`pow_iter_eq`), so the finite nets that witness conditional compactness
for `T` serve unchanged for `T^k`. -/

/-- `D`-measurability is unchanged by pulling back along any iterate of `T`. -/
theorem Factor.measurableSet_iterate_preimage_iff (D : Factor S) (k : ℕ) (s : Set S.X) :
    MeasurableSet[D.σ] (S.T^[k] ⁻¹' s) ↔ MeasurableSet[D.σ] s := by
  induction k generalizing s with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ', Set.preimage_comp, ih, D.invariant]

/-- Transport a factor of `S` to a factor of `S.pow k`.  The underlying σ-algebra is the same;
only the invariance proof changes, and `T`-invariance gives `T^k`-invariance. -/
def Factor.toPow (D : Factor S) (k : ℕ) : Factor (S.pow k) where
  σ := D.σ
  le := D.le
  invariant s := D.measurableSet_iterate_preimage_iff k s

@[simp] theorem Factor.toPow_σ (D : Factor S) (k : ℕ) : (D.toPow k).σ = D.σ := rfl

@[simp] theorem condInner_pow (D : Factor S) (k : ℕ) (f g : S.X → ℝ) :
    condInner (D.toPow k) f g = condInner D f g := rfl

@[simp] theorem condNorm_pow (D : Factor S) (k : ℕ) (f : S.X → ℝ) :
    condNorm (D.toPow k) f = condNorm D f := rfl

theorem MemModule.toPow {D E : Factor S} {k : ℕ} {f : S.X → ℝ} (h : MemModule D E f) :
    MemModule (D.toPow k) (E.toPow k) f :=
  ⟨h.meas, h.memLp, h.bddCondNorm⟩

/-- **Lemma `lem:powers`(1).**  Conditional compactness is inherited by `T^k`. -/
theorem CondCompact.pow {D E : Factor S} {f : S.X → ℝ} (hf : CondCompact D E f) (k : ℕ) :
    CondCompact (D.toPow k) (E.toPow k) f := by
  intro ε hε
  obtain ⟨r, g, hg, hcover⟩ := hf ε hε
  refine ⟨r, g, fun q => (hg q).toPow, fun n => ?_⟩
  obtain ⟨q, hq⟩ := hcover (k * n)
  refine ⟨q, ?_⟩
  rw [(S.pow_iter_eq k n)]
  exact hq

/-- **Lemma `lem:powers`(1).**  A compact extension for `T` is a compact extension for `T^k`. -/
theorem CompactExtension.pow {D E : Factor S} (h : CompactExtension D E) (k : ℕ) :
    CompactExtension (D.toPow k) (E.toPow k) := by
  intro f hmeas hmem ε hε
  obtain ⟨g, hg, hclose⟩ := h f hmeas hmem ε hε
  exact ⟨g, hg.pow k, hclose⟩

end MPS

end CantorSzemeredi

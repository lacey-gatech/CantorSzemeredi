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

end MPS

end CantorSzemeredi

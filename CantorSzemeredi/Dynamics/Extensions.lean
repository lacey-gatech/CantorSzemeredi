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

/-- Membership in `L²(E)`: the class Moreira's definition draws its approximants from.
Weaker than `MemModule`, which also asks for a bounded conditional norm. -/
structure MemL2 (E : Factor S) (f : S.X → ℝ) : Prop where
  /-- `f` is `E`-measurable. -/
  meas : AEStronglyMeasurable[E.σ] f S.m
  /-- `f` is square integrable. -/
  memLp : MemLp f 2 S.m

theorem MemModule.toMemL2 {D E : Factor S} {f : S.X → ℝ} (h : MemModule D E f) : MemL2 E f :=
  ⟨h.meas, h.memLp⟩

/-- **Definition `def:compact-extension`.**  `f` is *conditionally compact* if its orbit is
covered, to within `ε` in the conditional norm, by finitely many elements of `L²(E)`.

This is Moreira's Definition 6.11 verbatim, and the quantifier order is the point: the
approximant index `q` is chosen **inside** the almost-everywhere quantifier, so it may depend
on the fibre.  Demanding a single `q` for almost every `x` at once would be strictly
stronger, and in the wrong direction — a compact extension is what `lem:dichotomy`
*produces*, so strengthening the notion would put the dichotomy out of reach of the source it
is quoted from.  Nothing downstream needs the stronger form: the pigeonhole in the lifting
theorem (`thm:compact-extension`) chooses its index depending on `x`.

For the same reason the approximants are only asked to lie in `L²(E)`, not in the Hilbert
module, and the orbit is indexed by `ℕ`. -/
def CondCompact (D E : Factor S) (f : S.X → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (r : ℕ) (g : Fin r → S.X → ℝ), (∀ q, MemL2 E (g q)) ∧
    ∀ n : ℕ, ∀ᵐ x ∂S.m, ∃ q : Fin r, condNorm D (f ∘ S.T^[n] - g q) x < ε

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

theorem MemL2.toPow {E : Factor S} {k : ℕ} {f : S.X → ℝ} (h : MemL2 E f) :
    MemL2 (E.toPow k) f :=
  ⟨h.meas, h.memLp⟩

theorem MemModule.toPow {D E : Factor S} {k : ℕ} {f : S.X → ℝ} (h : MemModule D E f) :
    MemModule (D.toPow k) (E.toPow k) f :=
  ⟨h.meas, h.memLp, h.bddCondNorm⟩

/-- **Lemma `lem:powers`(1).**  Conditional compactness is inherited by `T^k`. -/
theorem CondCompact.pow {D E : Factor S} {f : S.X → ℝ} (hf : CondCompact D E f) (k : ℕ) :
    CondCompact (D.toPow k) (E.toPow k) f := by
  intro ε hε
  obtain ⟨r, g, hg, hcover⟩ := hf ε hε
  refine ⟨r, g, fun q => (hg q).toPow, fun n => ?_⟩
  have hiter : (S.pow k).T^[n] = S.T^[k * n] := by
    change (S.T^[k])^[n] = S.T^[k * n]
    rw [← Function.iterate_mul]
  filter_upwards [hcover (k * n)] with x hx
  obtain ⟨q, hq⟩ := hx
  exact ⟨q, by rwa [hiter]⟩

/-- **Lemma `lem:powers`(1).**  A compact extension for `T` is a compact extension for `T^k`. -/
theorem CompactExtension.pow {D E : Factor S} (h : CompactExtension D E) (k : ℕ) :
    CompactExtension (D.toPow k) (E.toPow k) := by
  intro f hmeas hmem ε hε
  obtain ⟨g, hg, hclose⟩ := h f hmeas hmem ε hε
  exact ⟨g, hg.pow k, hclose⟩

/-! ### `lem:powers`(2): conditional weak mixing passes to powers

The blueprint proves this by showing that a bounded non-negative sequence with Cesàro limit
zero tends to zero along a set of density one, and that a `k`-subsampling of a density-one set
again has density one.  That detour is avoidable.  Since the averaged quantities are
*non-negative*, the subsampled average is dominated pointwise by `k` times the full average:

  `N⁻¹ ∑_{n < N} φ_{kn} ≤ k · (kN)⁻¹ ∑_{m < kN} φ_m`,

because `{kn : n < N} ⊆ {m : m < kN}`.  Taking `L²(D)` norms and letting `N → ∞` finishes it,
with no density argument, no Cauchy–Schwarz, and no `L¹`/`L²` comparison. -/

/-- The subsampling bound: for a non-negative sequence, averaging over `{0, k, 2k, …}` costs at
most a factor `k` against averaging over everything. -/
theorem avg_subsample_le {φ : ℕ → ℝ} (hφ : ∀ n, 0 ≤ φ n) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, φ (k * n)
      ≤ k * ((k * N : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range (k * N), φ m := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hkN : 0 < k * N := Nat.mul_pos hk hN
  have hsub : ∑ n ∈ Finset.range N, φ (k * n) ≤ ∑ m ∈ Finset.range (k * N), φ m := by
    rw [← Finset.sum_image (f := φ) (g := fun n => k * n)]
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hφ m
      intro m hm
      simp only [Finset.mem_image, Finset.mem_range] at hm ⊢
      obtain ⟨n, hn, rfl⟩ := hm
      exact (Nat.mul_lt_mul_left (by omega)).2 hn
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left (by omega) hab
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcast : ((k * N : ℕ) : ℝ) = (k : ℝ) * (N : ℝ) := by push_cast; ring
  rw [hcast]
  rw [show (k : ℝ) * ((k : ℝ) * (N : ℝ))⁻¹ = (N : ℝ)⁻¹ by field_simp]
  exact mul_le_mul_of_nonneg_left hsub (by positivity)

/-- **Lemma `lem:powers`(2), for a pair.**  If the Cesàro means of `|⟨T^n f, g⟩_{E|D}|` tend to
`0` in `L²(D)`, then the same holds for `T^k`. -/
theorem tendsto_pow_pair {D : Factor S} {f g : S.X → ℝ}
    (h : Filter.Tendsto (fun N : ℕ => eLpNorm
        (fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, |condInner D (f ∘ S.T^[n]) g x|) 2 S.m)
      atTop (𝓝 0))
    {k : ℕ} (hk : 1 ≤ k) : Filter.Tendsto (fun N : ℕ => eLpNorm
        (fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, |condInner D (f ∘ (S.T^[k])^[n]) g x|) 2 S.m)
      atTop (𝓝 0) := by
  -- `(S.pow k).m`, `(S.pow k).T` and `(D.toPow k).σ` are definitionally `S.m`, `S.T^[k]` and
  -- `D.σ`; retype the goal once, so no `pow` friction remains.
  change Filter.Tendsto (fun N : ℕ => eLpNorm (fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      |condInner D (f ∘ (S.T^[k])^[n]) g x|) 2 S.m) atTop (𝓝 0)
  set φ : ℕ → S.X → ℝ := fun n x => |condInner D (f ∘ S.T^[n]) g x| with hφdef
  have hφ : ∀ n x, 0 ≤ φ n x := fun n x => abs_nonneg _
  -- The `T^k` averages, rewritten in terms of the `T` orbit.
  have hiter : ∀ n : ℕ, (S.T^[k])^[n] = S.T^[k * n] := fun n =>
    (Function.iterate_mul S.T k n).symm
  have hrewrite : ∀ N : ℕ,
      (fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          |condInner D (f ∘ (S.T^[k])^[n]) g x|)
        = fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, φ (k * n) x := by
    intro N
    funext x
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hiter n]
  -- Dominate the subsampled average by `k` times the full average, pointwise.
  set G : ℕ → S.X → ℝ := fun N x => ((N : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range N, φ m x with hG
  have hdom : ∀ N : ℕ, ∀ᵐ x ∂S.m,
      ‖(N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, φ (k * n) x‖ ≤ ‖((k : ℝ) • G (k * N)) x‖ := by
    intro N
    filter_upwards with x
    have h₁ := avg_subsample_le (φ := fun n => φ n x) (fun n => hφ n x) hk N
    have hnn : 0 ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, φ (k * n) x :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => hφ _ x)
    have hnn' : 0 ≤ ((k : ℝ) • G (k * N)) x := by
      refine mul_nonneg (by positivity) (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun m _ => hφ m x))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg hnn']
    simpa [hG, smul_eq_mul, mul_assoc] using h₁
  -- Measurability of the averaged quantities, needed for `eLpNorm_mono_ae`.
  have hmeasφ : ∀ n : ℕ, AEStronglyMeasurable (φ n) S.m := by
    intro n
    have hsm : StronglyMeasurable (condInner D (f ∘ S.T^[n]) g) :=
      stronglyMeasurable_condExp.mono D.le
    have habs : StronglyMeasurable fun x => |condInner D (f ∘ S.T^[n]) g x| := by
      simpa [Real.norm_eq_abs] using hsm.norm
    exact habs.aestronglyMeasurable
  have hmeasavg : ∀ N : ℕ,
      AEStronglyMeasurable (fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, φ (k * n) x) S.m := by
    intro N
    simp only [← Finset.sum_apply]
    exact (Finset.aestronglyMeasurable_sum _ fun n _ => hmeasφ (k * n)).const_mul _
  -- Take `L²` norms.
  have hsq : ∀ N : ℕ,
      eLpNorm (fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          |condInner D (f ∘ (S.T^[k])^[n]) g x|) 2 S.m
        ≤ (‖(k : ℝ)‖ₑ) * eLpNorm (G (k * N)) 2 S.m := by
    intro N
    rw [hrewrite N]
    refine le_trans (eLpNorm_mono_ae (hmeasavg N) (hdom N)) ?_
    rw [eLpNorm_const_smul]
  -- And pass to the limit along `N ↦ k * N`.
  have hkk : Filter.Tendsto (fun N : ℕ => k * N) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 fun b =>
      ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a hk)⟩
  have hGtend : Filter.Tendsto (fun N : ℕ => eLpNorm (G (k * N)) 2 S.m) atTop (𝓝 0) :=
    h.comp hkk
  have hbound : Filter.Tendsto
      (fun N : ℕ => (‖(k : ℝ)‖ₑ) * eLpNorm (G (k * N)) 2 S.m) atTop (𝓝 0) := by
    have hmul := ENNReal.Tendsto.const_mul (a := (‖(k : ℝ)‖ₑ)) hGtend (Or.inr (by simp))
    simpa using hmul
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun N => by simp) (Eventually.of_forall hsq)


/-- **Lemma `lem:powers`(2).**  Conditional weak mixing for `T` gives conditional weak mixing
for `T^k`. -/
theorem CondWeaklyMixing.pow {D : Factor S} {f : S.X → ℝ} (h : CondWeaklyMixing D f)
    {k : ℕ} (hk : 1 ≤ k) : CondWeaklyMixing (D.toPow k) (S := S.pow k) f :=
  tendsto_pow_pair h hk

end MPS

end CantorSzemeredi

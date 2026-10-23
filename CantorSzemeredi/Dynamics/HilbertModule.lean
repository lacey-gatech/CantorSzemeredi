/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.System

/-!
# The conditional inner product and the Hilbert module

Blueprint: `def:hilbert-module` and `lem:cond-cs` in `blueprint/src/chapter/mps.tex`.

For factors `D ⊆ E` of a system, the conditional inner product of `f, g ∈ L²(E)` is
`⟨f, g⟩_{E|D} = E(f * conj g | D) ∈ L²(D)`, with conditional norm `‖f‖_{E|D} = √⟨f,f⟩_{E|D}`.
The *Hilbert module* `L²(E|D)` consists of those `f` whose conditional norm is in `L^∞(D)`.

We work with real-valued functions throughout: the weakly mixing and compact extension
arguments only ever need real `f`, and this avoids carrying conjugates everywhere.

The conditional Cauchy–Schwarz inequality `|⟨f,g⟩| ≤ ‖f‖ ‖g‖` is proved pointwise a.e. from
the usual trick: `E((t f + g)² | D) ≥ 0` for every rational `t`, so the discriminant of the
resulting quadratic is `≤ 0`.
-/

namespace CantorSzemeredi

open MeasureTheory

namespace MPS

variable {S : MPS}

/-- The conditional inner product `⟨f, g⟩_{E|D} = E(f g | D)`. -/
noncomputable def condInner (D : Factor S) (f g : S.X → ℝ) : S.X → ℝ :=
  S.m[f * g|D.σ]

/-- The conditional norm `‖f‖_{E|D} = √ E(f² | D)`. -/
noncomputable def condNorm (D : Factor S) (f : S.X → ℝ) : S.X → ℝ :=
  fun x => Real.sqrt (condInner D f f x)

theorem condInner_self_nonneg (D : Factor S) (f : S.X → ℝ) :
    0 ≤ᵐ[S.m] condInner D f f :=
  condExp_nonneg (by filter_upwards with x using mul_self_nonneg (f x))

theorem condNorm_nonneg (D : Factor S) (f : S.X → ℝ) (x : S.X) : 0 ≤ condNorm D f x :=
  Real.sqrt_nonneg _

theorem condNorm_sq (D : Factor S) (f : S.X → ℝ) :
    (fun x => condNorm D f x ^ 2) =ᵐ[S.m] condInner D f f := by
  filter_upwards [condInner_self_nonneg D f] with x hx
  rw [condNorm, Real.sq_sqrt hx]

/-! ### Linearity of conditional expectation, in the form used below -/

/-- `E(a u + b v | D) = a E(u|D) + b E(v|D)`. -/
theorem condExp_lin (D : Factor S) {u v : S.X → ℝ} (hu : Integrable u S.m)
    (hv : Integrable v S.m) (a b : ℝ) :
    S.m[fun x => a * u x + b * v x|D.σ]
      =ᵐ[S.m] fun x => a * (S.m[u|D.σ]) x + b * (S.m[v|D.σ]) x := by
  have hau : Integrable (fun x => a * u x) S.m := hu.const_mul a
  have hbv : Integrable (fun x => b * v x) S.m := hv.const_mul b
  have hadd : S.m[(fun x => a * u x) + fun x => b * v x|D.σ]
      =ᵐ[S.m] S.m[fun x => a * u x|D.σ] + S.m[fun x => b * v x|D.σ] :=
    condExp_add hau hbv D.σ
  have ha : S.m[fun x => a * u x|D.σ] =ᵐ[S.m] fun x => a * (S.m[u|D.σ]) x := by
    have hsm : (fun x => a * u x) = a • u := by funext x; simp [smul_eq_mul]
    rw [hsm]
    filter_upwards [condExp_smul (μ := S.m) (m := D.σ) a u] with x hx
    simpa [smul_eq_mul] using hx
  have hb : S.m[fun x => b * v x|D.σ] =ᵐ[S.m] fun x => b * (S.m[v|D.σ]) x := by
    have hsm : (fun x => b * v x) = b • v := by funext x; simp [smul_eq_mul]
    rw [hsm]
    filter_upwards [condExp_smul (μ := S.m) (m := D.σ) b v] with x hx
    simpa [smul_eq_mul] using hx
  filter_upwards [hadd, ha, hb] with x hx hax hbx
  have hx' : (S.m[fun x => a * u x + b * v x|D.σ]) x
      = (S.m[fun x => a * u x|D.σ]) x + (S.m[fun x => b * v x|D.σ]) x := hx
  rw [hx', hax, hbx]

/-- `E(a u + b v + w | D) = a E(u|D) + b E(v|D) + E(w|D)`, the shape the discriminant argument
needs. -/
theorem condExp_lin3 (D : Factor S) {u v w : S.X → ℝ} (hu : Integrable u S.m)
    (hv : Integrable v S.m) (hw : Integrable w S.m) (a b : ℝ) :
    S.m[fun x => a * u x + b * v x + w x|D.σ]
      =ᵐ[S.m] fun x => a * (S.m[u|D.σ]) x + b * (S.m[v|D.σ]) x + (S.m[w|D.σ]) x := by
  have huv : Integrable (fun x => a * u x + b * v x) S.m := (hu.const_mul a).add (hv.const_mul b)
  have hadd : S.m[(fun x => a * u x + b * v x) + w|D.σ]
      =ᵐ[S.m] S.m[fun x => a * u x + b * v x|D.σ] + S.m[w|D.σ] := condExp_add huv hw D.σ
  filter_upwards [hadd, condExp_lin D hu hv a b] with x hx hlin
  have hx' : (S.m[fun x => a * u x + b * v x + w x|D.σ]) x
      = (S.m[fun x => a * u x + b * v x|D.σ]) x + (S.m[w|D.σ]) x := hx
  rw [hx', hlin]

/-! ### Conditional Cauchy–Schwarz

The discriminant argument.  `E((t f + g)² | D) ≥ 0` for each fixed `t`, but the full-measure
set on which that holds depends on `t`; so we run `t` over the *rationals*, intersect the
countably many full-measure sets, and extend to all real `t` by continuity.  Then
`discrim_le_zero` gives `⟨f,g⟩² ≤ ‖f‖² ‖g‖²` pointwise. -/

/-- The quadratic `t ↦ E(f²|D) t² + 2 E(fg|D) t + E(g²|D)` is non-negative, almost everywhere
simultaneously for all real `t`. -/
theorem condInner_quadratic_nonneg (D : Factor S) {f g : S.X → ℝ}
    (hff : Integrable (f * f) S.m) (hgg : Integrable (g * g) S.m)
    (hfg : Integrable (f * g) S.m) :
    ∀ᵐ x ∂S.m, ∀ t : ℝ,
      0 ≤ condInner D f f x * t ^ 2 + 2 * condInner D f g x * t + condInner D g g x := by
  -- For a fixed rational `t`.
  have hrat : ∀ t : ℚ, ∀ᵐ x ∂S.m,
      0 ≤ condInner D f f x * (t : ℝ) ^ 2 + 2 * condInner D f g x * (t : ℝ)
            + condInner D g g x := by
    intro t
    set c : ℝ := (t : ℝ) with hc
    have hsq : ∀ x, c ^ 2 * (f * f) x + (2 * c) * (f * g) x + (g * g) x
        = (c * f x + g x) ^ 2 := by
      intro x
      simp only [Pi.mul_apply]
      ring
    have hnn : (0 : S.X → ℝ) ≤ᵐ[S.m]
        S.m[fun x => c ^ 2 * (f * f) x + (2 * c) * (f * g) x + (g * g) x|D.σ] := by
      refine condExp_nonneg ?_
      filter_upwards with x
      rw [hsq x]
      positivity
    have hlin : S.m[fun x => c ^ 2 * (f * f) x + (2 * c) * (f * g) x + (g * g) x|D.σ]
        =ᵐ[S.m] fun x => c ^ 2 * condInner D f f x + (2 * c) * condInner D f g x
            + condInner D g g x :=
      condExp_lin3 D hff hfg hgg (c ^ 2) (2 * c)
    filter_upwards [hnn, hlin] with x hx h₁
    rw [h₁] at hx
    simp only [Pi.zero_apply] at hx
    linarith
  -- Intersect over the rationals, then extend to the reals by continuity.
  rw [← ae_all_iff] at hrat
  filter_upwards [hrat] with x hx t
  have hcont : Continuous fun s : ℝ =>
      condInner D f f x * s ^ 2 + 2 * condInner D f g x * s + condInner D g g x := by
    fun_prop
  have hdense : ∀ s ∈ Set.range ((↑) : ℚ → ℝ),
      0 ≤ condInner D f f x * s ^ 2 + 2 * condInner D f g x * s + condInner D g g x := by
    rintro _ ⟨q, rfl⟩
    exact hx q
  have := (isClosed_le continuous_const hcont).closure_subset_iff.2 hdense
  exact this (by rw [Rat.denseRange_cast.closure_eq]; trivial)

/-- **Lemma `lem:cond-cs`, conditional Cauchy–Schwarz.**
`|⟨f,g⟩_{E|D}| ≤ ‖f‖_{E|D} ‖g‖_{E|D}` almost everywhere. -/
theorem abs_condInner_le (D : Factor S) {f g : S.X → ℝ}
    (hff : Integrable (f * f) S.m) (hgg : Integrable (g * g) S.m)
    (hfg : Integrable (f * g) S.m) :
    ∀ᵐ x ∂S.m, |condInner D f g x| ≤ condNorm D f x * condNorm D g x := by
  filter_upwards [condInner_quadratic_nonneg D hff hgg hfg,
    condInner_self_nonneg D f, condInner_self_nonneg D g] with x hquad hA hB
  set A := condInner D f f x
  set B := condInner D g g x
  set Cc := condInner D f g x
  have hdisc : discrim A (2 * Cc) B ≤ 0 :=
    discrim_le_zero (fun t => by have := hquad t; linarith)
  have hsq : Cc ^ 2 ≤ A * B := by
    rw [discrim] at hdisc
    nlinarith
  calc |Cc| = Real.sqrt (Cc ^ 2) := (Real.sqrt_sq_eq_abs Cc).symm
    _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA _
    _ = condNorm D f x * condNorm D g x := rfl

end MPS

end CantorSzemeredi

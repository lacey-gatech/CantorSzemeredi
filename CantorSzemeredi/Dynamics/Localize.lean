/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.CondHS
import CantorSzemeredi.Dynamics.Atomless

/-!
# Localization of compact extensions

Blueprint: `blueprint/src/chapter/compact.tex`, Lemma `lem:localize` (Moreira, Lemma 8.4.3).

For a compact extension `E | D` and `f ∈ L²(E)`, and every `η > 0`, there is a set `A ∈ D`
with `m(Aᶜ) ≤ η` such that `f · 1_A` is conditionally compact.

The proof approximates `f` by conditionally compact `g_k` with rapidly shrinking
tolerances, keeps the points where the conditional errors are small (a `D`-set, by
Chebyshev), and then builds an approximating net for `f · 1_A` from the net of `g_k` and
the zero function.
-/

namespace CantorSzemeredi

open MeasureTheory Filter Topology

namespace MPS

variable {S : MPS}

/-- Conditional expectation commutes with every iterate of `T`. -/
theorem condExp_comp_iterate (D : Factor S) (n : ℕ) :
    ∀ {a : S.X → ℝ}, Integrable a S.m →
      S.m[a ∘ S.T^[n] | D.σ] =ᵐ[S.m] (S.m[a | D.σ]) ∘ S.T^[n] := by
  induction n with
  | zero => intro a _; simp
  | succ n ih =>
    intro a ha
    have hTm : MeasurePreserving S.T S.m S.m := S.measurePreserving
    have ha' : Integrable (a ∘ S.T) S.m :=
      (hTm.integrable_comp ha.aestronglyMeasurable).2 ha
    have hTn := (S.measurePreserving_T_iterate n).quasiMeasurePreserving
    rw [Function.iterate_succ', ← Function.comp_assoc, ← Function.comp_assoc]
    exact (ih ha').trans (hTn.ae_eq_comp (Factor.condExp_comp D ha).symm)

/-- The conditional norm is equivariant under `T^n`, almost everywhere. -/
theorem condNorm_comp_iterate (D : Factor S) (n : ℕ) {v : S.X → ℝ} (hv : MemLp v 2 S.m) :
    condNorm D (v ∘ S.T^[n]) =ᵐ[S.m] (condNorm D v) ∘ S.T^[n] := by
  have hvv : Integrable (v * v) S.m := hv.integrable_mul hv
  have h1 : condInner D (v ∘ S.T^[n]) (v ∘ S.T^[n])
      =ᵐ[S.m] (condInner D v v) ∘ S.T^[n] :=
    condExp_comp_iterate D n hvv
  filter_upwards [h1] with x hx
  change Real.sqrt (condInner D (v ∘ S.T^[n]) (v ∘ S.T^[n]) x)
    = Real.sqrt (condInner D v v (S.T^[n] x))
  rw [hx]
  rfl

/-- A `D`-set pulls out of the conditional norm: `‖1_B u‖ = 1_B ‖u‖`. -/
theorem condNorm_indicator (D : Factor S) {B : Set S.X} (hB : MeasurableSet[D.σ] B)
    {u : S.X → ℝ} (hu : MemLp u 2 S.m) :
    ∀ᵐ x ∂S.m, condNorm D (B.indicator u) x = B.indicator (condNorm D u) x := by
  have hγ : StronglyMeasurable[D.σ] (B.indicator (1 : S.X → ℝ)) :=
    stronglyMeasurable_const.indicator hB
  have hwm : MemLp (B.indicator u) 2 S.m := MemLp.indicator (D.le B hB).nullMeasurableSet hu
  have hfun : B.indicator u = fun y => B.indicator (1 : S.X → ℝ) y * u y := by
    funext y
    by_cases hy : y ∈ B <;> simp [hy]
  have hγu : Integrable ((fun y => B.indicator (1 : S.X → ℝ) y * u y)
      * fun y => B.indicator (1 : S.X → ℝ) y * u y) S.m := by
    rw [← hfun]
    exact hwm.integrable_mul hwm
  filter_upwards [condNorm_mul_left D hγ hγu (hu.integrable_mul hu)] with x hx
  rw [hfun, hx]
  by_cases hy : x ∈ B <;> simp [hy]

/-- On `B`, the conditional norm of `1_B u - h` is at most that of `u - h`. -/
theorem condNorm_indicator_sub_le (D : Factor S) {B : Set S.X} (hB : MeasurableSet[D.σ] B)
    {u h : S.X → ℝ} (hu : MemLp u 2 S.m) (hh : MemLp h 2 S.m) :
    ∀ᵐ x ∂S.m, x ∈ B → condNorm D (B.indicator u - h) x ≤ condNorm D (u - h) x := by
  have hBc : MeasurableSet[D.σ] Bᶜ := hB.compl
  have hfun : B.indicator u - h = B.indicator (u - h) + Bᶜ.indicator (-h) := by
    funext y
    by_cases hy : y ∈ B <;> simp [hy]
  have hm1 : MemLp (B.indicator (u - h)) 2 S.m :=
    MemLp.indicator (D.le B hB).nullMeasurableSet (hu.sub hh)
  have hm2 : MemLp (Bᶜ.indicator (-h)) 2 S.m :=
    MemLp.indicator (D.le Bᶜ hBc).nullMeasurableSet hh.neg
  filter_upwards [condNorm_add_le D hm1 hm2, condNorm_indicator D hB (hu.sub hh),
    condNorm_indicator D hBc hh.neg] with x hx h1 h2 hxB
  rw [hfun]
  refine hx.trans (le_of_eq ?_)
  have hxBc : x ∉ Bᶜ := fun hc => hc hxB
  rw [h1, h2, Set.indicator_of_mem hxB, Set.indicator_of_notMem hxBc, add_zero]

/-- **Lemma `lem:localize`.**  For a compact extension `E | D`, every `f ∈ L²(E)` and every
`η > 0`, there is `A ∈ D` with `m(Aᶜ) ≤ η` such that `f · 1_A` is conditionally compact. -/
theorem exists_condCompact_restrict (D E : Factor S) (hE : CompactExtension D E)
    {f : S.X → ℝ} (hfE : AEStronglyMeasurable[E.σ] f S.m) (hf : MemLp f 2 S.m)
    {η : ℝ} (hη : 0 < η) :
    ∃ A : Set S.X, MeasurableSet[D.σ] A ∧ S.m Aᶜ ≤ ENNReal.ofReal η ∧
      CondCompact D E (A.indicator f) := by
  -- Step 1: conditionally compact approximants `g k` with tolerances `√η / 4^(k+1)`.
  have hsqrt : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  obtain ⟨g, hgC, hgL⟩ : ∃ g : ℕ → S.X → ℝ, (∀ k, CondCompact D E (g k)) ∧
      ∀ k, eLpNorm (f - g k) 2 S.m ≤ ENNReal.ofReal (Real.sqrt η * (1 / 4 : ℝ) ^ (k + 1)) := by
    have := fun k : ℕ => hE f hfE hf (Real.sqrt η * (1 / 4 : ℝ) ^ (k + 1))
      (mul_pos hsqrt (by positivity))
    choose g hgC hgL using this
    exact ⟨g, hgC, hgL⟩
  have hgf : ∀ k, MemLp (f - g k) 2 S.m := fun k =>
    lt_of_le_of_lt (hgL k) ENNReal.ofReal_lt_top
  have hgL2 : ∀ k, MemLp (g k) 2 S.m := fun k => by
    simpa using hf.sub (hgf k)
  -- Step 2: the `D`-sets `Ak k` where the conditional error is at most `(1/2)^(k+1)`.
  set Ak : ℕ → Set S.X := fun k => {x | condNorm D (f - g k) x ≤ (1 / 2 : ℝ) ^ (k + 1)}
    with hAk_def
  have hmeas : ∀ v : S.X → ℝ, Measurable[D.σ] (condNorm D v) := fun v => by
    unfold condNorm condInner
    exact Real.continuous_sqrt.measurable.comp (stronglyMeasurable_condExp (m := D.σ)).measurable
  have hAkD : ∀ k, MeasurableSet[D.σ] (Ak k) := fun k =>
    hmeas (f - g k) measurableSet_Iic
  -- Chebyshev: the bad set has small measure.
  have hbad : ∀ k, S.m (Ak k)ᶜ ≤ ENNReal.ofReal (η * (1 / 2 : ℝ) ^ (k + 1)) := by
    intro k
    have hFint : Integrable (fun x => condNorm D (f - g k) x ^ 2) S.m :=
      integrable_condExp.congr (condNorm_sq D (f - g k)).symm
    have hFnn : 0 ≤ᵐ[S.m] (fun x => condNorm D (f - g k) x ^ 2) :=
      Filter.Eventually.of_forall fun x => sq_nonneg _
    have hcheb := mul_meas_ge_le_integral_of_nonneg hFnn hFint
      (((1 / 2 : ℝ) ^ (k + 1)) ^ 2)
    have hsub : (Ak k)ᶜ ⊆ {x | ((1 / 2 : ℝ) ^ (k + 1)) ^ 2 ≤ condNorm D (f - g k) x ^ 2} := by
      intro x hx
      simp only [hAk_def, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
      have hc : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (k + 1) := by positivity
      have hcn := condNorm_nonneg D (f - g k) x
      change ((1 / 2 : ℝ) ^ (k + 1)) ^ 2 ≤ condNorm D (f - g k) x ^ 2
      nlinarith
    have hint : ∫ x, condNorm D (f - g k) x ^ 2 ∂S.m
        = (eLpNorm (f - g k) 2 S.m).toReal ^ 2 := by
      rw [← integral_sq_eq_eLpNorm_sq (hgf k)]
      have h1 : ∫ x, condNorm D (f - g k) x ^ 2 ∂S.m
          = ∫ x, condInner D (f - g k) (f - g k) x ∂S.m :=
        integral_congr_ae (condNorm_sq D (f - g k))
      rw [h1]
      unfold condInner
      rw [integral_condExp D.le]
      congr 1
      funext x
      simp only [Pi.mul_apply, sq]
    have htn : (eLpNorm (f - g k) 2 S.m).toReal ≤ Real.sqrt η * (1 / 4 : ℝ) ^ (k + 1) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hgL k)
    have hmeasure : S.m.real (Ak k)ᶜ ≤ η * (1 / 2 : ℝ) ^ (k + 1) := by
      have hmono := measureReal_mono hsub (measure_ne_top S.m _)
      set c := (1 / 2 : ℝ) ^ (k + 1) with hc_def
      have hcpos : 0 < c ^ 2 := by positivity
      have hq : ((1 / 4 : ℝ) ^ (k + 1)) ^ 2 ≤ (1 / 2 : ℝ) ^ (k + 1) * c ^ 2 := by
        have e1 : ((1 / 4 : ℝ) ^ (k + 1)) ^ 2 = (1 / 16 : ℝ) ^ (k + 1) := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        have e2 : (1 / 2 : ℝ) ^ (k + 1) * c ^ 2 = (1 / 8 : ℝ) ^ (k + 1) := by
          rw [hc_def, ← pow_mul, show (1 / 8 : ℝ) = (1 / 2) ^ 3 by norm_num, ← pow_mul,
            ← pow_add]
          congr 1
          ring
        rw [e1, e2]
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have ht2 : (eLpNorm (f - g k) 2 S.m).toReal ^ 2
          ≤ η * ((1 / 4 : ℝ) ^ (k + 1)) ^ 2 := by
        have := pow_le_pow_left₀ ENNReal.toReal_nonneg htn 2
        have hsq : (Real.sqrt η * (1 / 4 : ℝ) ^ (k + 1)) ^ 2
            = η * ((1 / 4 : ℝ) ^ (k + 1)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hη.le]
        linarith
      have key : c ^ 2 * S.m.real (Ak k)ᶜ ≤ c ^ 2 * (η * (1 / 2 : ℝ) ^ (k + 1)) := by
        calc c ^ 2 * S.m.real (Ak k)ᶜ
            ≤ c ^ 2 * S.m.real {x | c ^ 2 ≤ condNorm D (f - g k) x ^ 2} :=
              mul_le_mul_of_nonneg_left hmono hcpos.le
          _ ≤ ∫ x, condNorm D (f - g k) x ^ 2 ∂S.m := hcheb
          _ = (eLpNorm (f - g k) 2 S.m).toReal ^ 2 := hint
          _ ≤ η * ((1 / 4 : ℝ) ^ (k + 1)) ^ 2 := ht2
          _ ≤ η * ((1 / 2 : ℝ) ^ (k + 1) * c ^ 2) :=
              mul_le_mul_of_nonneg_left hq hη.le
          _ = c ^ 2 * (η * (1 / 2 : ℝ) ^ (k + 1)) := by ring
      exact le_of_mul_le_mul_left key hcpos
    rw [← ENNReal.ofReal_toReal (measure_ne_top S.m _)]
    exact ENNReal.ofReal_le_ofReal (by simpa [measureReal_def] using hmeasure)
  -- Step 3: the set `A`, its measure, and its `D`-measurability.
  set A : Set S.X := ⋂ k, Ak k with hA_def
  have hAD : MeasurableSet[D.σ] A := MeasurableSet.iInter fun k => hAkD k
  have hAm : S.m Aᶜ ≤ ENNReal.ofReal η := by
    have hAc : Aᶜ = ⋃ k, (Ak k)ᶜ := by
      rw [hA_def, Set.compl_iInter]
    have hsum : Summable (fun k : ℕ => η * (1 / 2 : ℝ) ^ (k + 1)) := by
      convert (summable_geometric_two.mul_left (η / 2)) using 1
      funext k
      ring
    have hgeo : ∑' k : ℕ, η * (1 / 2 : ℝ) ^ (k + 1) = η := by
      rw [show (fun k : ℕ => η * (1 / 2 : ℝ) ^ (k + 1)) = fun k => (η / 2) * (1 / 2 : ℝ) ^ k
        from by funext k; ring, tsum_mul_left, tsum_geometric_two]
      ring
    rw [hAc]
    calc S.m (⋃ k, (Ak k)ᶜ) ≤ ∑' k, S.m (Ak k)ᶜ := measure_iUnion_le _
      _ ≤ ∑' k, ENNReal.ofReal (η * (1 / 2 : ℝ) ^ (k + 1)) := ENNReal.tsum_le_tsum hbad
      _ = ENNReal.ofReal (∑' k : ℕ, η * (1 / 2 : ℝ) ^ (k + 1)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum).symm
      _ = ENNReal.ofReal η := by rw [hgeo]
  refine ⟨A, hAD, hAm, ?_⟩
  -- Step 4: `f · 1_A` is conditionally compact.
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
  have hck : (1 / 2 : ℝ) ^ (k + 1) < ε / 2 := by
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
  obtain ⟨r, h, hhE, hnet⟩ := hgC k (ε / 2) (half_pos hε)
  refine ⟨r + 1, Fin.cons 0 h, ?_, ?_⟩
  · intro q
    refine Fin.cases ?_ (fun q => ?_) q
    · simp only [Fin.cons_zero]
      exact ⟨(@stronglyMeasurable_const _ _ E.σ _ 0).aestronglyMeasurable, memLp_const (0 : ℝ)⟩
    · simpa only [Fin.cons_succ] using hhE q
  intro n
  have hB : MeasurableSet[D.σ] (S.T^[n] ⁻¹' A) :=
    (Factor.measurableSet_iterate_preimage_iff D n A).2 hAD
  have hAeq : A.indicator f ∘ S.T^[n] = (S.T^[n] ⁻¹' A).indicator (f ∘ S.T^[n]) := by
    funext x
    by_cases hx : S.T^[n] x ∈ A <;> simp [hx]
  have hu : MemLp (f ∘ S.T^[n]) 2 S.m := hf.comp_measurePreserving (S.measurePreserving_T_iterate n)
  have hm1 : ∀ q0 : Fin r, MemLp ((f - g k) ∘ S.T^[n]) 2 S.m := fun _ =>
    (hgf k).comp_measurePreserving (S.measurePreserving_T_iterate n)
  have hm2 : ∀ q0 : Fin r, MemLp (g k ∘ S.T^[n] - h q0) 2 S.m := fun q0 =>
    ((hgL2 k).comp_measurePreserving (S.measurePreserving_T_iterate n)).sub (hhE q0).memLp
  have hsum : ∀ q0 : Fin r, (f ∘ S.T^[n] - h q0 : S.X → ℝ) = (f - g k) ∘ S.T^[n]
      + (g k ∘ S.T^[n] - h q0) := by
    intro q0; funext x; simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply]; ring
  rw [hAeq]
  have h1 : ∀ᵐ x ∂S.m, ∀ q0 : Fin r, x ∈ S.T^[n] ⁻¹' A →
      condNorm D ((S.T^[n] ⁻¹' A).indicator (f ∘ S.T^[n]) - h q0) x
        ≤ condNorm D (f ∘ S.T^[n] - h q0) x :=
    ae_all_iff.2 fun q0 => condNorm_indicator_sub_le D hB hu (hhE q0).memLp
  have h2 : ∀ᵐ x ∂S.m, ∀ q0 : Fin r,
      condNorm D (f ∘ S.T^[n] - h q0) x
        ≤ condNorm D ((f - g k) ∘ S.T^[n]) x + condNorm D (g k ∘ S.T^[n] - h q0) x := by
    refine ae_all_iff.2 fun q0 => ?_
    filter_upwards [condNorm_add_le D (hm1 q0) (hm2 q0)] with x hx
    rw [← hsum q0] at hx
    exact hx
  have h3 : ∀ᵐ x ∂S.m, x ∈ S.T^[n] ⁻¹' A →
      condNorm D ((f - g k) ∘ S.T^[n]) x ≤ (1 / 2 : ℝ) ^ (k + 1) := by
    filter_upwards [condNorm_comp_iterate D n (hgf k)] with x hx hxB
    rw [hx]
    have hmem : S.T^[n] x ∈ Ak k := by
      have := Set.mem_iInter.1 hxB k
      exact this
    exact hmem
  have h4 : ∀ᵐ x ∂S.m, ∃ q0 : Fin r, condNorm D (g k ∘ S.T^[n] - h q0) x < ε / 2 := by
    simpa using hnet n
  filter_upwards [h1, h2, h3, h4, condNorm_indicator D hB hu] with x hx1 hx2 hx3 hx4 hx5
  by_cases hxB : x ∈ S.T^[n] ⁻¹' A
  · obtain ⟨q0, hq0⟩ := hx4
    refine ⟨q0.succ, ?_⟩
    simp only [Fin.cons_succ]
    have e1 := hx1 q0 hxB
    have e2 := hx2 q0
    have e3 := hx3 hxB
    linarith
  · refine ⟨0, ?_⟩
    simp only [Fin.cons_zero, sub_zero]
    rw [hx5, Set.indicator_of_notMem hxB]
    exact hε

end MPS

end CantorSzemeredi

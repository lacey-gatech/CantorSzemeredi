module

public import CantorSzemeredi.Proof.Structure
public import CantorSzemeredi.Proof.Dichotomy.Defs
public import CantorSzemeredi.Proof.Dichotomy.Kernel
public import CantorSzemeredi.Proof.Dichotomy.Truncate
public import CantorSzemeredi.Proof.Dichotomy.Cut
public import CantorSzemeredi.Proof.Dichotomy.Class
public import CantorSzemeredi.Proof.Dichotomy.Sigma
public import CantorSzemeredi.Proof.Dichotomy.FibreCompact
public import Mathlib

/-!
# The dichotomy

## Main statement

* `dichotomy_of_fibreTB`: `DichotomyStatement`, assuming only the fibrewise total boundedness
  lemma `ae_fibreTB_of_kernel_data` in the form `hL8` (for every system, factor and data satisfying
  the conclusion
  `KernelData` of `exists_kernel_data`, `FibreTB D f' x` holds for almost every `x`).

## Proof

If `D` is not weakly mixing in the top factor, `exists_kernel_data` gives `f'`.  Clamping
`f'` at a large `K` gives a bounded function `u` that is still fibrewise totally bounded and not
a.e. `D`-measurable (otherwise `f' = lim u_K` would be `D`-measurable with `E(f'|D) = 0`).  The cut
lemma gives a `D`-set `B` of almost full measure with `1_B u ∈ compactClass D`; for `B` small
enough `1_B u` is still not `D`-measurable.  It is measurable for `compactFactor D`, so
`D.σ < (compactFactor D).σ`, and `compactExtension_compactFactor` finishes.
-/

@[expose] public section

namespace CantorSzemeredi.Proof

open MeasureTheory ProbabilityTheory CSZPort CSZPort.MPS Filter Topology

variable {S : MPS} [StandardBorelSpace S.X]

/-- The conclusion of `exists_kernel_data` as a predicate on the data. -/
def KernelData (D : Factor S) (φ : ℝ) (H₀ H₁ : S.X × S.X → ℝ) (a f' : S.X → ℝ) : Prop :=
  StronglyMeasurable H₀ ∧ StronglyMeasurable H₁ ∧
      MemLp H₀ 2 (joining D) ∧ MemLp H₁ 2 (joining D) ∧
      (∀ n : ℤ, (fun p => H₀ ((prodSystem D).iter n p)) =ᵐ[joining D]
        fun p => Real.cos (n * φ) * H₀ p - Real.sin (n * φ) * H₁ p) ∧
      (∀ n : ℤ, (fun p => H₁ ((prodSystem D).iter n p)) =ᵐ[joining D]
        fun p => Real.sin (n * φ) * H₀ p + Real.cos (n * φ) * H₁ p) ∧
      Measurable a ∧ (∀ x, |a x| ≤ 1) ∧
      f' = condIntegralOp D H₀ a ∧ Measurable f' ∧ Integrable f' S.m ∧
      ¬ (f' =ᵐ[S.m] 0) ∧ (S.m[f'|D.σ] =ᵐ[S.m] 0) ∧
      ∀ n : ℤ, (fun x => f' (S.iter n x)) =ᵐ[S.m] fun x =>
        Real.cos (n * φ) * condIntegralOp D H₀ (fun z => a (S.iter n z)) x
          - Real.sin (n * φ) * condIntegralOp D H₁ (fun z => a (S.iter n z)) x

/-- The function `f'` of the kernel data is in `L²`. -/
theorem memLp_two_of_kernelData (D : Factor S) {φ : ℝ} {H₀ H₁ : S.X × S.X → ℝ}
    {a f' : S.X → ℝ} (h : KernelData D φ H₀ H₁ a f') : MemLp f' 2 S.m := by
  obtain ⟨hH₀, -, hm₀, -, -, -, ha, hab, hfdef, hfm, -⟩ := h
  refine (memLp_hsRow D hH₀ hm₀).mono hfm.aestronglyMeasurable ?_
  filter_upwards [ae_memLp_row D hH₀ hm₀] with x hx
  have hamem : MemLp a 2 (condKernel D x) :=
    MemLp.of_bound ha.aestronglyMeasurable 1 (Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hab y)
  have h1 := abs_condIntegralOp_le D hx hamem
  have hn1 : fibreNorm D a x ≤ 1 := by
    unfold fibreNorm
    apply Real.sqrt_le_one.2
    calc ∫ y, a y ^ 2 ∂(condKernel D x) ≤ ∫ _y, (1 : ℝ) ∂(condKernel D x) :=
          integral_mono hamem.integrable_sq (integrable_const _) fun y => by
            have := hab y
            nlinarith [abs_nonneg (a y), sq_abs (a y)]
      _ = 1 := by simp
  have h2 : hsRow D H₀ x ≥ 0 := hsRow_nonneg D H₀ x
  rw [hfdef]
  have : |condIntegralOp D H₀ a x| ≤ hsRow D H₀ x := by
    refine h1.trans ?_
    nlinarith [fibreNorm_nonneg D a x]
  simpa [Real.norm_eq_abs, abs_of_nonneg h2] using this

/-- Clamping preserves fibrewise total boundedness (clamping is 1-Lipschitz). -/
theorem fibreTB_clampFn (D : Factor S) {f : S.X → ℝ} (K : ℝ) (hL2 : MemLp f 2 S.m)
    (hTB : ∀ᵐ x ∂S.m, FibreTB D f x) : ∀ᵐ x ∂S.m, FibreTB D (clampFn K f) x := by
  have hall : ∀ᵐ x ∂S.m, ∀ n : ℤ, MemLp (f ∘ S.iter n) 2 (condKernel D x) :=
    ae_all_iff.2 fun n => ae_memLp_condKernel' D
      (hL2.comp_measurePreserving (S.measurePreserving_iter n))
  filter_upwards [hTB, hall] with x hx hmem ε hε
  obtain ⟨S', hS'⟩ := hx ε hε
  refine ⟨S', fun n => ?_⟩
  obtain ⟨s, hs, hlt⟩ := hS' n
  refine ⟨s, hs, lt_of_le_of_lt ?_ hlt⟩
  unfold fibreNorm
  apply Real.sqrt_le_sqrt
  have hd : MemLp (f ∘ S.iter n - f ∘ S.iter s) 2 (condKernel D x) := (hmem n).sub (hmem s)
  refine integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _)
    hd.integrable_sq (Eventually.of_forall fun y => ?_)
  have hl := (lipschitzWith_clamp (-K) K).dist_le_mul (f (S.iter n y)) (f (S.iter s y))
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hl
  simp only [Pi.sub_apply, Function.comp_apply, clampFn, min_comm K]
  exact sq_le_sq.2 hl

omit [StandardBorelSpace S.X] in
/-- For large `K`, the clamp of `f` is not a.e. `D`-measurable. -/
theorem exists_clamp_not_ae (D : Factor S) {f : S.X → ℝ} (hf : Measurable f)
    (hL2 : MemLp f 2 S.m) (hcond : S.m[f|D.σ] =ᵐ[S.m] 0) (hne : ¬ f =ᵐ[S.m] 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ¬ (clampFn K f =ᵐ[S.m] S.m[clampFn K f|D.σ]) := by
  by_contra hcon
  push Not at hcon
  have hfi : Integrable f S.m := hL2.integrable (by norm_num)
  have hbound : ∀ K : ℝ, 0 ≤ K → eLpNorm f 1 S.m ≤ 2 * eLpNorm (f - clampFn K f) 1 S.m := by
    intro K hK
    have hui : Integrable (clampFn K f) S.m :=
      (memLp_two_of_bounded (measurable_clampFn hf)
        fun x => (clamp_facts K (f x) hK).2.1).integrable (by norm_num)
    have hsplit : f = (f - clampFn K f) + clampFn K f := by ext x; simp
    have h1 : eLpNorm f 1 S.m ≤ eLpNorm (f - clampFn K f) 1 S.m + eLpNorm (clampFn K f) 1 S.m := by
      conv_lhs => rw [hsplit]
      exact eLpNorm_add_le le_rfl
    have h2 : eLpNorm (clampFn K f) 1 S.m = eLpNorm (S.m[clampFn K f|D.σ]) 1 S.m :=
      eLpNorm_congr_ae (hcon K hK)
    have h3 : S.m[clampFn K f - f|D.σ] =ᵐ[S.m] S.m[clampFn K f|D.σ] := by
      filter_upwards [condExp_sub hui hfi D.σ, hcond] with x hx h0
      rw [hx]; simp [h0]
    have h4 : eLpNorm (S.m[clampFn K f|D.σ]) 1 S.m ≤ eLpNorm (f - clampFn K f) 1 S.m := by
      rw [← eLpNorm_congr_ae h3, eLpNorm_sub_comm (f := f) (g := clampFn K f)]
      exact eLpNorm_condExp_le_eLpNorm _ le_rfl
    calc eLpNorm f 1 S.m ≤ _ := h1
      _ ≤ eLpNorm (f - clampFn K f) 1 S.m + eLpNorm (f - clampFn K f) 1 S.m := by
          gcongr; rw [h2]; exact h4
      _ = 2 * _ := by rw [two_mul]
  have hlim : Tendsto (fun n : ℕ => eLpNorm (f - clampFn (n : ℝ) f) 1 S.m) atTop (𝓝 0) := by
    have hfun : (fun n : ℕ => eLpNorm (f - clampFn (n : ℝ) f) 1 S.m) =
        fun n : ℕ => ∫⁻ x, ‖(f - clampFn (n : ℝ) f) x‖ₑ ∂S.m := by
      funext n
      exact eLpNorm_one_eq_lintegral_enorm (hf.sub (measurable_clampFn hf)).aestronglyMeasurable
    rw [hfun]
    have := tendsto_lintegral_of_dominated_convergence (μ := S.m)
      (F := fun (n : ℕ) x => ‖(f - clampFn (n : ℝ) f) x‖ₑ) (f := fun _ => (0 : ENNReal))
      (bound := fun x => ‖f x‖ₑ)
      (fun n => (hf.sub (measurable_clampFn hf)).enorm)
      (fun n => Eventually.of_forall fun x => by
        have := (clamp_facts (n : ℝ) (f x) n.cast_nonneg).1
        simp only [Pi.sub_apply, clampFn, enorm_eq_nnnorm]
        exact ENNReal.coe_le_coe.2 (by
          rw [← NNReal.coe_le_coe]; simpa [Real.norm_eq_abs] using this))
      hfi.hasFiniteIntegral.ne
      (Eventually.of_forall fun x => by
        obtain ⟨N, hN⟩ := exists_nat_ge |f x|
        refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
        have hle : |f x| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
        have := (clamp_facts (n : ℝ) (f x) n.cast_nonneg).2.2 hle
        simp [clampFn, this])
    simpa using this
  have hle : eLpNorm f 1 S.m ≤ 0 := by
    have h2 := ENNReal.Tendsto.const_mul hlim (Or.inr (by simp : (2 : ENNReal) ≠ ⊤))
    rw [mul_zero] at h2
    exact ge_of_tendsto' h2 fun n => hbound n n.cast_nonneg
  exact hne ((eLpNorm_eq_zero_iff one_ne_zero).1 (le_antisymm hle bot_le))

omit [StandardBorelSpace S.X] in
/-- If `u` is not a.e. `D`-measurable, then cutting `u` to a `D`-set of large enough measure
leaves it non-`D`-measurable. -/
theorem exists_eta_not_measurable (D : Factor S) {u : S.X → ℝ} (hu : Measurable u) {K : ℝ}
    (hub : ∀ x, |u x| ≤ K) (hne : ¬ (u =ᵐ[S.m] S.m[u|D.σ])) :
    ∃ η : ℝ, 0 < η ∧ ∀ B : Set S.X, MeasurableSet[D.σ] B → S.m Bᶜ < ENNReal.ofReal η →
      ¬ Measurable[D.σ] (B.indicator u) := by
  have hui : Integrable u S.m :=
    (memLp_two_of_bounded hu hub).integrable (by norm_num)
  set N : Set S.X := {x | u x ≠ (S.m[u|D.σ]) x} with hN
  have hNpos : S.m N ≠ 0 := fun h0 => hne (ae_iff.2 (by simpa [hN] using h0))
  have hNfin : S.m N ≠ ⊤ := measure_ne_top _ _
  refine ⟨(S.m N).toReal, ENNReal.toReal_pos hNpos hNfin, fun B hB hBη hg => ?_⟩
  rw [ENNReal.ofReal_toReal hNfin] at hBη
  have hgi : Integrable (B.indicator u) S.m := hui.indicator (D.le _ hB)
  have h1 : S.m[B.indicator u|D.σ] = B.indicator u :=
    condExp_of_stronglyMeasurable D.le hg.stronglyMeasurable hgi
  have h2 := condExp_indicator hui hB
  rw [h1] at h2
  have : S.m N ≤ S.m Bᶜ := by
    refine measure_mono_ae ?_
    filter_upwards [h2] with x hx hxN
    by_contra hxB
    rw [Set.mem_compl_iff, not_not] at hxB
    apply hxN
    simpa [Set.indicator_of_mem hxB] using hx
  exact absurd hBη (not_lt.2 this)

/-- **Assembly.**  The Furstenberg–Zimmer dichotomy, assuming only the fibrewise total
boundedness lemma `ae_fibreTB_of_kernel_data`: for every system on a standard Borel space, every
factor `D` and every
`(φ, H₀, H₁, a, f')` satisfying the conclusion `KernelData` of `exists_kernel_data`,
`FibreTB D f' x` holds for almost every `x`. -/
theorem dichotomy_of_fibreTB
    (hL8 : ∀ (S : CSZPort.MPS.{0}) [StandardBorelSpace S.X] (D : Factor S) (φ : ℝ)
      (H₀ H₁ : S.X × S.X → ℝ) (a f' : S.X → ℝ), KernelData D φ H₀ H₁ a f' →
        ∀ᵐ x ∂S.m, FibreTB D f' x) :
    DichotomyStatement := by
  intro S _ D _
  by_cases h : WeaklyMixingExtension D (Factor.top S)
  · exact Or.inl h
  · right
    obtain ⟨φ, H₀, H₁, a, f', hkd⟩ := exists_kernel_data D h
    have hTB := hL8 S D φ H₀ H₁ a f' hkd
    have hL2 := memLp_two_of_kernelData D hkd
    obtain ⟨-, -, -, -, -, -, -, -, -, hfm, -, hfne, hfcond, -⟩ := hkd
    obtain ⟨K, hK0, hK⟩ := exists_clamp_not_ae D hfm hL2 hfcond hfne
    have hum := measurable_clampFn (K := K) hfm
    have hub : ∀ x, |clampFn K f' x| ≤ K := fun x => (clamp_facts K (f' x) hK0).2.1
    have hTBu := fibreTB_clampFn D K hL2 hTB
    obtain ⟨η, hη, hηB⟩ := exists_eta_not_measurable D hum hub hK
    obtain ⟨B, hBm, -, hBη, hg⟩ := exists_cut_set D hum hub hTBu hη
    refine ⟨compactFactor D, ?_, compactExtension_compactFactor D⟩
    refine lt_of_le_of_ne (le_compactFactor D) fun heq => hηB B hBm hBη ?_
    have := measurable_of_mem_compactClass hg
    rw [← heq] at this
    exact this

/-- **The Furstenberg–Zimmer dichotomy** (unconditional). -/
theorem dichotomy : DichotomyStatement :=
  dichotomy_of_fibreTB fun S _ D φ _ _ a f' hkd => by
    obtain ⟨hH₀, hH₁, hm₀, hm₁, -, -, ha, hab, -, -, -, -, -, hf⟩ := hkd
    exact ae_fibreTB_of_kernel_data D φ hH₀ hH₁ hm₀ hm₁ ha hab hf

end CantorSzemeredi.Proof

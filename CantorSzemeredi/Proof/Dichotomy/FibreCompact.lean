module

public import CantorSzemeredi.Proof.Dichotomy.Defs
public import CantorSzemeredi.Proof.Dichotomy.FibreConst
public import CantorSzemeredi.Proof.Dichotomy.Kernel
public import CantorSzemeredi.Port.Dynamics.Fibre
public import CantorSzemeredi.Port.Analysis.HilbertSchmidt
public import Mathlib

/-!
# Fibrewise total boundedness of the orbit

* `fibreTB_aux` : abstract fixed-fibre statement.  If `A₀ A₁` are compact operators on
  `L²(ν; ℂ)` (`ν` a probability measure), `β n` lie in the unit ball, `|c n|, |s n| ≤ 1`, and the
  functions `g n` are a.e. equal to `c n • Re (A₀ (β n)) - s n • Re (A₁ (β n))`, then the family
  `g` has a finite `ε`-net inside itself for the `L²(ν)` norm.  (Image of a compact set under a
  continuous map is compact, hence totally bounded; a subset of a totally bounded set is totally
  bounded and has a finite net inside itself.)
* `ae_fibreTB_of_orbit_data` : for the data of `exists_kernel_data`
  (`f' ∘ iterⁿ = cₙ Φ_{H₀}(a ∘ iterⁿ) - sₙ
  Φ_{H₁}(a ∘ iterⁿ)` a.e.), `FibreTB D f' x` for almost every `x`.  The complex operators
  `A_i = integralKernelL` of the (real) kernels `H_i` on the fibre `m_x` are compact for a.e.
  `x` (`ae_isCompactOperator_fibre`), and the rows are computed by `ae_ae_condIntegralOp_orbit`.
* `ae_fibreTB_of_kernel_data` : the same with `cₙ = cos (nφ)`, `sₙ = sin (nφ)`, as produced by
  `exists_kernel_data`.
-/

@[expose] public section

namespace CantorSzemeredi.Proof

open MeasureTheory ProbabilityTheory CSZPort CSZPort.MPS HilbertSchmidt

section Abstract

variable {X : Type*} [MeasurableSpace X] (ρ : Measure X)

/-- The real part, as a continuous `ℝ`-linear map `L²(ρ; ℂ) → L²(ρ; ℝ)`. -/
noncomputable def reLp : Lp ℂ 2 ρ →L[ℝ] Lp ℝ 2 ρ :=
  ContinuousLinearMap.compLpL 2 ρ Complex.reCLM

theorem coeFn_reLp (u : Lp ℂ 2 ρ) : ∀ᵐ y ∂ρ, reLp ρ u y = (u y).re :=
  ContinuousLinearMap.coeFn_compLpL Complex.reCLM u

/-- The `L²` norm of a real `Lp` element, as the square root of the integral of the square. -/
theorem norm_lp_real_eq (u : Lp ℝ 2 ρ) : ‖u‖ = Real.sqrt (∫ y, (u y) ^ 2 ∂ρ) := by
  have h : ‖u‖ ^ 2 = ∫ y, (u y) ^ 2 ∂ρ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [sq]
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- Abstract fixed-fibre total boundedness. -/
theorem fibreTB_aux [IsProbabilityMeasure ρ] (A₀ A₁ : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ)
    (h₀ : IsCompactOperator A₀) (h₁ : IsCompactOperator A₁)
    (g : ℤ → X → ℝ) (c s : ℤ → ℝ) (hc : ∀ n, |c n| ≤ 1) (hs : ∀ n, |s n| ≤ 1)
    (β : ℤ → Lp ℂ 2 ρ) (hβ : ∀ n, ‖β n‖ ≤ 1)
    (h : ∀ n, g n =ᵐ[ρ] ⇑(c n • reLp ρ (A₀ (β n)) - s n • reLp ρ (A₁ (β n)))) :
    ∀ ε : ℝ, 0 < ε → ∃ S' : Finset ℤ, ∀ n, ∃ k ∈ S',
      Real.sqrt (∫ y, (g n y - g k y) ^ 2 ∂ρ) < ε := by
  intro ε hε
  set e : ℤ → Lp ℝ 2 ρ := fun n => c n • reLp ρ (A₀ (β n)) - s n • reLp ρ (A₁ (β n)) with he
  have K0 := h₀.isCompact_closure_image_closedBall 1
  have K1 := h₁.isCompact_closure_image_closedBall 1
  set Ψ : ℝ × ℝ × Lp ℂ 2 ρ × Lp ℂ 2 ρ → Lp ℝ 2 ρ :=
    fun q => q.1 • reLp ρ q.2.2.1 - q.2.1 • reLp ρ q.2.2.2 with hΨ
  have hΨc : Continuous Ψ := by
    simp only [hΨ]; fun_prop
  have hK : IsCompact (Ψ '' (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 ×ˢ
      closure (⇑A₀ '' Metric.closedBall 0 1) ×ˢ closure (⇑A₁ '' Metric.closedBall 0 1))) :=
    (isCompact_Icc.prod (isCompact_Icc.prod (K0.prod K1))).image hΨc
  have hsub : Set.range e ⊆ Ψ '' (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 ×ˢ
      closure (⇑A₀ '' Metric.closedBall 0 1) ×ˢ closure (⇑A₁ '' Metric.closedBall 0 1)) := by
    rintro _ ⟨n, rfl⟩
    refine ⟨(c n, s n, A₀ (β n), A₁ (β n)), ⟨abs_le.1 (hc n), abs_le.1 (hs n),
      subset_closure ⟨β n, ?_, rfl⟩, subset_closure ⟨β n, ?_, rfl⟩⟩, rfl⟩
    · simpa using hβ n
    · simpa using hβ n
  obtain ⟨t, hts, htf, hcov⟩ := Metric.finite_approx_of_totallyBounded
    (hK.totallyBounded.subset hsub) ε hε
  have hts' : t ⊆ e '' Set.univ := by rwa [Set.image_univ]
  obtain ⟨t', -, ht'f, ht'cov⟩ := Set.exists_subset_image_finite_and
    (f := e) (s := Set.univ) (p := fun t => Set.range e ⊆ ⋃ y ∈ t, Metric.ball y ε) |>.1
    ⟨t, hts', htf, hcov⟩
  refine ⟨ht'f.toFinset, fun n => ?_⟩
  obtain ⟨y, ⟨k, hk, rfl⟩, hy⟩ := Set.mem_iUnion₂.1 (ht'cov ⟨n, rfl⟩)
  refine ⟨k, ht'f.mem_toFinset.2 hk, ?_⟩
  have hae : (fun y => g n y - g k y) =ᵐ[ρ] ⇑(e n - e k) := by
    filter_upwards [h n, h k, Lp.coeFn_sub (e n) (e k)] with y h1 h2 h3
    rw [h3, Pi.sub_apply, h1, h2]
  have hint : ∫ y, (g n y - g k y) ^ 2 ∂ρ = ∫ y, ((e n - e k) y) ^ 2 ∂ρ :=
    integral_congr_ae (hae.mono fun y hy => by
      have hy' : g n y - g k y = (e n - e k) y := hy
      show (g n y - g k y) ^ 2 = ((e n - e k) y) ^ 2
      rw [hy'])
  rw [hint, ← norm_lp_real_eq, ← dist_eq_norm]
  exact Metric.mem_ball.1 hy

/-- The real part of the fibre operator applied to a bounded real function, computed on the
row. -/
theorem coeFn_reLp_integralKernelL [IsProbabilityMeasure ρ] {k : X × X → ℝ}
    (hk : MemLp (fun p => (k p : ℂ)) 2 (ρ.prod ρ)) (b : X → ℝ)
    (hb : MemLp (fun z => (b z : ℂ)) 2 ρ) :
    ∀ᵐ y ∂ρ, reLp ρ (integralKernelL hk (hb.toLp _)) y = ∫ z, k (y, z) * b z ∂ρ := by
  have hβ := hb.coeFn_toLp
  filter_upwards [coeFn_reLp ρ (integralKernelL hk (hb.toLp _)),
    (memLp_integralKernel hk (Lp.memLp (hb.toLp _))).coeFn_toLp] with y h1 h2
  rw [h1, integralKernelL_apply, h2, integralKernel]
  have : ∫ z, (k (y, z) : ℂ) * (hb.toLp _ : Lp ℂ 2 ρ) z ∂ρ
      = ∫ z, (((k (y, z) * b z : ℝ)) : ℂ) ∂ρ := by
    refine integral_congr_ae (hβ.mono fun z hz => ?_)
    have hz' : ((hb.toLp _ : Lp ℂ 2 ρ) z) = (b z : ℂ) := hz
    simp only [hz', Complex.ofReal_mul]
  rw [this, integral_complex_ofReal, Complex.ofReal_re]

end Abstract

variable {S : MPS} [StandardBorelSpace S.X]

/-- **Orbit form.**  For almost every `x` the `ℤ`-orbit of `f'` is totally bounded in the
fibre norm at `x`, for the data of `exists_kernel_data` with arbitrary coefficient sequences bounded
by `1`. -/
theorem ae_fibreTB_of_orbit_data (D : Factor S) (c s : ℤ → ℝ)
    (hc : ∀ n, |c n| ≤ 1) (hs : ∀ n, |s n| ≤ 1)
    {H₀ H₁ : S.X × S.X → ℝ} (hH₀ : StronglyMeasurable H₀) (hH₁ : StronglyMeasurable H₁)
    (hm₀ : MemLp H₀ 2 (joining D)) (hm₁ : MemLp H₁ 2 (joining D))
    {a f' : S.X → ℝ} (ha : Measurable a) (hab : ∀ x, |a x| ≤ 1)
    (hf : ∀ n : ℤ, (fun x => f' (S.iter n x)) =ᵐ[S.m] fun x =>
      c n * condIntegralOp D H₀ (fun z => a (S.iter n z)) x
        - s n * condIntegralOp D H₁ (fun z => a (S.iter n z)) x) :
    ∀ᵐ x ∂S.m, FibreTB D f' x := by
  have hs₀ : StronglyMeasurable (fun p => (H₀ p : ℂ)) :=
    Complex.continuous_ofReal.comp_stronglyMeasurable hH₀
  have hs₁ : StronglyMeasurable (fun p => (H₁ p : ℂ)) :=
    Complex.continuous_ofReal.comp_stronglyMeasurable hH₁
  filter_upwards [ae_ae_condIntegralOp_orbit D c s H₀ H₁ a f' hf,
    ae_isCompactOperator_fibre D hs₀ hm₀.ofReal,
    ae_isCompactOperator_fibre D hs₁ hm₁.ofReal] with x hrow hx0 hx1
  obtain ⟨hk0, hcp0⟩ := hx0
  obtain ⟨hk1, hcp1⟩ := hx1
  intro ε hε
  have hbm : ∀ n : ℤ, MemLp (fun z => ((a (S.iter n z) : ℝ) : ℂ)) 2 (condKernel D x) := by
    intro n
    refine MemLp.of_bound ?_ 1 (Filter.Eventually.of_forall fun z => ?_)
    · exact (Complex.measurable_ofReal.comp
        (ha.comp (S.measurable_iter n))).aestronglyMeasurable
    · simpa [Complex.norm_real] using hab _
  have hβ : ∀ n : ℤ, ‖(hbm n).toLp _‖ ≤ 1 := by
    intro n
    have := Lp.norm_le_of_ae_bound (f := (hbm n).toLp _) (C := 1) zero_le_one
      ((hbm n).coeFn_toLp.mono fun z hz => by
        rw [hz]; simpa [Complex.norm_real] using hab _)
    rwa [show ((measureUnivNNReal (condKernel D x) : NNReal) : ℝ) = 1 by
      simp [measureUnivNNReal], Real.one_rpow, one_mul] at this
  obtain ⟨S', hS'⟩ := fibreTB_aux (condKernel D x) (integralKernelL hk0) (integralKernelL hk1)
    hcp0 hcp1 (fun n y => f' (S.iter n y)) c s hc hs (fun n => (hbm n).toLp _) hβ (by
      intro n
      filter_upwards [hrow n,
        Lp.coeFn_sub (c n • reLp (condKernel D x) (integralKernelL hk0 ((hbm n).toLp _)))
          (s n • reLp (condKernel D x) (integralKernelL hk1 ((hbm n).toLp _))),
        Lp.coeFn_smul (c n) (reLp (condKernel D x) (integralKernelL hk0 ((hbm n).toLp _))),
        Lp.coeFn_smul (s n) (reLp (condKernel D x) (integralKernelL hk1 ((hbm n).toLp _))),
        coeFn_reLp_integralKernelL (condKernel D x) hk0 _ (hbm n),
        coeFn_reLp_integralKernelL (condKernel D x) hk1 _ (hbm n)]
        with y h1 h2 h3 h4 h5 h6
      rw [h2, Pi.sub_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h5, h6, h1]
      simp only [smul_eq_mul])
    ε hε
  refine ⟨S', fun n => ?_⟩
  obtain ⟨k, hk, hlt⟩ := hS' n
  exact ⟨k, hk, by simpa [fibreNorm] using hlt⟩

/-- For the data of `exists_kernel_data`: for almost every `x`, `FibreTB D f' x`.
Only the hypotheses of the conclusion of `exists_kernel_data` that are needed are assumed. -/
theorem ae_fibreTB_of_kernel_data (D : Factor S) (φ : ℝ)
    {H₀ H₁ : S.X × S.X → ℝ} (hH₀ : StronglyMeasurable H₀) (hH₁ : StronglyMeasurable H₁)
    (hm₀ : MemLp H₀ 2 (joining D)) (hm₁ : MemLp H₁ 2 (joining D))
    {a f' : S.X → ℝ} (ha : Measurable a) (hab : ∀ x, |a x| ≤ 1)
    (hf : ∀ n : ℤ, (fun x => f' (S.iter n x)) =ᵐ[S.m] fun x =>
      Real.cos (n * φ) * condIntegralOp D H₀ (fun z => a (S.iter n z)) x
        - Real.sin (n * φ) * condIntegralOp D H₁ (fun z => a (S.iter n z)) x) :
    ∀ᵐ x ∂S.m, FibreTB D f' x :=
  ae_fibreTB_of_orbit_data D (fun n => Real.cos (n * φ)) (fun n => Real.sin (n * φ))
    (fun n => Real.abs_cos_le_one _) (fun n => Real.abs_sin_le_one _) hH₀ hH₁ hm₀ hm₁ ha hab hf

end CantorSzemeredi.Proof

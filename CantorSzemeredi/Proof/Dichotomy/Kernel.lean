module

public import CantorSzemeredi.Port.Dynamics.CondHS
public import CantorSzemeredi.Port.Dynamics.Joining
public import CantorSzemeredi.Port.Dynamics.Atomless
public import CantorSzemeredi.Port.Dynamics.Koopman
public import CantorSzemeredi.Port.Dynamics.Extensions
public import CantorSzemeredi.Port.Dynamics.CompactSystem
public import CantorSzemeredi.Port.Analysis.HilbertSchmidt
public import CantorSzemeredi.Proof.Dichotomy.Truncate
public import CantorSzemeredi.Proof.Dichotomy.Eigen
public import CantorSzemeredi.Proof.Dichotomy.FibreConst
public import Mathlib

/-!
# Kernel data of the atom

* `condIntegralOp_congr_ae_kernel` : `Φ_H b` only sees the `λ`-a.e. class of the kernel `H`.
* `condIntegralOp_comp_iter` : the orbit identity for `n : ℤ`,
  `(Φ_H a) ∘ Tⁿ =ᵐ Φ_{H ∘ Rⁿ} (a ∘ Tⁿ)` with `Rⁿ = (prodSystem D).iter n`.
* `condIntegralOp_comb_ae` : fibrewise linearity in the kernel.
* `exists_kernel_data` : from `¬ WeaklyMixingExtension D top` we get a real `φ`, kernels
  `H₀ H₁` and a bounded measurable `a` with `f' = Φ_{H₀} a` not a.e. zero, `m[f'|D] = 0` and
  `f' ∘ Tⁿ = cos(nφ) Φ_{H₀}(a ∘ Tⁿ) - sin(nφ) Φ_{H₁}(a ∘ Tⁿ)` for all `n : ℤ`
  (the eigenvalue of `H = H₀ + i H₁` is `e^{iφ}`, i.e. `φ = 2πθ`).
-/

@[expose] public section

namespace CantorSzemeredi.Proof

open MeasureTheory ProbabilityTheory CSZPort CSZPort.MPS

variable {S : MPS} [StandardBorelSpace S.X]

/-- `Φ_H b` only depends on the `λ`-a.e. class of `H`. -/
theorem condIntegralOp_congr_ae_kernel (D : Factor S) {H H' : S.X × S.X → ℝ}
    (h : H =ᵐ[joining D] H') (b : S.X → ℝ) :
    ∀ᵐ x ∂S.m, condIntegralOp D H b x = condIntegralOp D H' b x := by
  rw [← compProd_condKernel_eq_joining D] at h
  filter_upwards [Measure.ae_ae_of_ae_compProd h] with x hx
  unfold condIntegralOp
  refine integral_congr_ae ?_
  filter_upwards [hx] with y hy
  rw [hy]

/-- Fibrewise linearity of the operator in the kernel. -/
theorem condIntegralOp_comb_ae (D : Factor S) {H₀ H₁ : S.X × S.X → ℝ}
    (hH₀ : StronglyMeasurable H₀) (hH₁ : StronglyMeasurable H₁)
    (hm₀ : MemLp H₀ 2 (joining D)) (hm₁ : MemLp H₁ 2 (joining D))
    {b : S.X → ℝ} (hb : Measurable b) {C : ℝ} (hbb : ∀ x, |b x| ≤ C) (c s : ℝ) :
    ∀ᵐ x ∂S.m, condIntegralOp D (fun p => c * H₀ p - s * H₁ p) b x
      = c * condIntegralOp D H₀ b x - s * condIntegralOp D H₁ b x := by
  have hbl : ∀ ν : Measure S.X, IsProbabilityMeasure ν → MemLp b 2 ν := fun ν _ =>
    memLp_of_bounded (a := -C) (b := C) (Filter.Eventually.of_forall fun x => by
      rw [Set.mem_Icc]; exact abs_le.1 (hbb x)) hb.aestronglyMeasurable 2
  filter_upwards [ae_memLp_row D hH₀ hm₀, ae_memLp_row D hH₁ hm₁] with x h0 h1
  have i0 : Integrable (fun y => H₀ (x, y) * b y) (condKernel D x) :=
    h0.integrable_mul (hbl _ inferInstance)
  have i1 : Integrable (fun y => H₁ (x, y) * b y) (condKernel D x) :=
    h1.integrable_mul (hbl _ inferInstance)
  unfold condIntegralOp
  have : (fun y => (c * H₀ (x, y) - s * H₁ (x, y)) * b y)
      = fun y => c * (H₀ (x, y) * b y) - s * (H₁ (x, y) * b y) := by
    funext y; ring
  simp only [this]
  rw [integral_sub (i0.const_mul c) (i1.const_mul s), integral_const_mul, integral_const_mul]

/-- **The orbit identity over `ℤ`.** -/
theorem condIntegralOp_comp_iter (D : Factor S) {H : S.X × S.X → ℝ} {a : S.X → ℝ} {Ca : ℝ}
    (hHm : StronglyMeasurable H) (hH : MemLp H 2 (joining D))
    (ham : StronglyMeasurable a) (hab : ∀ y, |a y| ≤ Ca) (n : ℤ) :
    (condIntegralOp D H a) ∘ S.iter n
      =ᵐ[S.m] condIntegralOp D (fun p => H ((prodSystem D).iter n p)) (fun y => a (S.iter n y)) := by
  cases n with
  | ofNat k =>
    have := condIntegralOp_comp_iterate D hHm hH ham hab k
    simpa using this
  | negSucc j =>
    set k := j + 1 with hk
    have hneg : Int.negSucc j = -((k : ℕ) : ℤ) := by simp [hk, Int.negSucc_eq]
    rw [hneg]
    set P := prodSystem D with hP
    have hPiter : P.iter (-((k : ℕ) : ℤ)) = P.Tinv^[k] := P.iter_neg_natCast k
    have hSiter : S.iter (-((k : ℕ) : ℤ)) = S.Tinv^[k] := S.iter_neg_natCast k
    rw [hPiter, hSiter]
    have hPmp : MeasurePreserving (P.Tinv^[k]) (joining D) (joining D) :=
      P.measurePreserving_Tinv_iterate k
    have hH'm : StronglyMeasurable fun p => H (P.Tinv^[k] p) :=
      hHm.comp_measurable (P.measurable_Tinv.iterate k)
    have hH' : MemLp (fun p => H (P.Tinv^[k] p)) 2 (joining D) :=
      hH.comp_measurePreserving hPmp
    have ha' : StronglyMeasurable fun y => a (S.Tinv^[k] y) :=
      ham.comp_measurable (S.measurable_Tinv.iterate k)
    have h1 := condIntegralOp_comp_iterate D hH'm hH' ha' (fun y => hab _) k
    have hK : (fun p => (fun p => H (P.Tinv^[k] p)) ((prodMap S)^[k] p)) = H := by
      funext p
      have : P.Tinv^[k] ((prodMap S)^[k] p) = p := P.leftInverse_Tinv.iterate k p
      simp only [this]
    have hA : (fun y => (fun y => a (S.Tinv^[k] y)) (S.T^[k] y)) = a := by
      funext y
      have : S.Tinv^[k] (S.T^[k] y) = y := S.leftInverse_Tinv.iterate k y
      simp only [this]
    rw [hK, hA] at h1
    have h2 := (S.measurePreserving_Tinv_iterate k).quasiMeasurePreserving.ae_eq_comp h1
    refine h2.symm.trans (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply]
    have : S.T^[k] (S.Tinv^[k] x) = x := S.rightInverse_Tinv.iterate k x
    simp only [this]
    rfl

/-! ### The eigenfunction as a pair of real kernels -/

section Eigen

variable (D : Factor S)

/-- Phase normalisation: an eigenvector orthogonal to the tensors whose real part is not a.e. 0. -/
theorem exists_eigenvector_re_ne_zero (ε : ℂ)
    (h : ∃ w : Lp ℂ 2 (prodSystem D).m, w ≠ 0 ∧ (prodSystem D).koopman w = ε • w ∧
      ∀ g : Lp ℂ 2 (prodSystem D).m, IsTensorD D g → inner ℂ g w = 0) :
    ∃ w : Lp ℂ 2 (prodSystem D).m, (prodSystem D).koopman w = ε • w ∧
      (∀ g : Lp ℂ 2 (prodSystem D).m, IsTensorD D g → inner ℂ g w = 0) ∧
      ¬ ((fun p => (w p).re) =ᵐ[(prodSystem D).m] 0) := by
  obtain ⟨w0, hw0, hwe0, hwperp0⟩ := h
  by_cases hre : (fun p => (w0 p).re) =ᵐ[(prodSystem D).m] 0
  · refine ⟨Complex.I • w0, ?_, ?_, ?_⟩
    · rw [map_smul, hwe0, smul_comm]
    · intro g hg
      rw [inner_smul_right, hwperp0 g hg, mul_zero]
    · intro hcon
      apply hw0
      refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
      filter_upwards [hre, hcon, Lp.coeFn_smul Complex.I w0] with p h1 h2 h3
      rw [h3] at h2
      simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, one_mul, zero_sub, Pi.zero_apply, neg_eq_zero] at h1 h2
      exact Complex.ext (by simpa using h1) (by simpa using h2)
  · exact ⟨w0, hwe0, hwperp0, hre⟩

omit [StandardBorelSpace S.X] in
theorem eigen_zpow {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) (w : H) (ε : ℂ) (hε : ε ≠ 0) (h : U w = ε • w) (n : ℤ) :
    (U ^ n) w = ε ^ n • w := by
  have hinv : (U⁻¹) w = ε⁻¹ • w := by
    apply U.injective
    have h1 : U (U⁻¹ w) = w := by
      change (U * U⁻¹) w = w
      rw [mul_inv_cancel]; rfl
    rw [h1, map_smul, h, smul_smul, inv_mul_cancel₀ hε, one_smul]
  induction n using Int.induction_on with
  | zero => simp
  | succ m ih =>
    rw [zpow_add_one]
    change (U ^ (m : ℤ)) (U w) = _
    rw [h, map_smul, ih, smul_smul, zpow_add_one₀ hε, mul_comm]
  | pred m ih =>
    rw [zpow_sub_one]
    change (U ^ (-(m : ℤ))) (U⁻¹ w) = _
    rw [hinv, map_smul, ih, smul_smul, zpow_sub_one₀ hε, mul_comm]

/-- Real and imaginary parts of the eigenfunction, as strongly measurable kernels in `L²(λ)` with
the rotation law `H₀ ∘ Rⁿ = cos(nφ) H₀ - sin(nφ) H₁`, `H₁ ∘ Rⁿ = sin(nφ) H₀ + cos(nφ) H₁`. -/
theorem exists_real_kernels (ε : ℂ) (hε : ‖ε‖ = 1) (w : Lp ℂ 2 (prodSystem D).m)
    (hw : (prodSystem D).koopman w = ε • w) :
    ∃ (φ : ℝ) (H₀ H₁ : S.X × S.X → ℝ), StronglyMeasurable H₀ ∧ StronglyMeasurable H₁ ∧
      MemLp H₀ 2 (joining D) ∧ MemLp H₁ 2 (joining D) ∧
      (w =ᵐ[joining D] fun p => ((H₀ p : ℝ) : ℂ) + ((H₁ p : ℝ) : ℂ) * Complex.I) ∧
      (∀ n : ℤ, (fun p => H₀ ((prodSystem D).iter n p)) =ᵐ[joining D]
        fun p => Real.cos (n * φ) * H₀ p - Real.sin (n * φ) * H₁ p) ∧
      (∀ n : ℤ, (fun p => H₁ ((prodSystem D).iter n p)) =ᵐ[joining D]
        fun p => Real.sin (n * φ) * H₀ p + Real.cos (n * φ) * H₁ p) := by
  have hε0 : ε ≠ 0 := by intro h0; rw [h0] at hε; simp at hε
  set φ : ℝ := Complex.arg ε with hφ
  have hεexp : ε = Complex.exp (φ * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I ε
    rw [hε, Complex.ofReal_one, one_mul] at this
    exact this.symm
  set W : (prodSystem D).X → ℂ := (Lp.aestronglyMeasurable w).mk w with hWdef
  have hWsm : StronglyMeasurable W := (Lp.aestronglyMeasurable w).stronglyMeasurable_mk
  have hwW : w =ᵐ[joining D] W := (Lp.aestronglyMeasurable w).ae_eq_mk
  have hWmem : MemLp W 2 (joining D) := (Lp.memLp w).ae_eq hwW
  have hrot : ∀ n : ℤ, ∀ᵐ p ∂(joining D), W ((prodSystem D).iter n p) = ε ^ n * W p := by
    intro n
    have h1 := (prodSystem D).coeFn_koopman_zpow n w
    have h2 := eigen_zpow (prodSystem D).koopman w ε hε0 hw n
    have h3 : (((prodSystem D).koopman ^ n) w) =ᵐ[joining D] fun p => ε ^ n * w p := by
      rw [h2]
      filter_upwards [Lp.coeFn_smul (ε ^ n) w] with p hp
      simp only [Pi.smul_apply, smul_eq_mul] at hp
      exact hp
    have h4 := ((prodSystem D).measurePreserving_iter n).quasiMeasurePreserving.ae_eq_comp hwW
    filter_upwards [h1, h3, h4, hwW] with p a b c d
    simp only [Function.comp_apply] at c
    exact c.symm.trans (a.symm.trans (b.trans (by rw [d])))
  refine ⟨φ, fun p => (W p).re, fun p => (W p).im,
    Complex.continuous_re.comp_stronglyMeasurable hWsm,
    Complex.continuous_im.comp_stronglyMeasurable hWsm, hWmem.re, hWmem.im, ?_, ?_, ?_⟩
  · filter_upwards [hwW] with p hp
    rw [hp]
    exact (Complex.re_add_im (W p)).symm
  · intro n
    filter_upwards [hrot n] with p hp
    have hn : ε ^ n = ((Real.cos (n * φ) : ℝ) : ℂ) + ((Real.sin (n * φ) : ℝ) : ℂ) * Complex.I := by
      rw [hεexp, ← Complex.exp_int_mul]
      have : (n : ℂ) * (φ * Complex.I) = ((n * φ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    show (W ((prodSystem D).iter n p)).re
      = Real.cos (n * φ) * (W p).re - Real.sin (n * φ) * (W p).im
    rw [hp, hn]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.mul_im,
      Complex.add_im, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · intro n
    filter_upwards [hrot n] with p hp
    have hn : ε ^ n = ((Real.cos (n * φ) : ℝ) : ℂ) + ((Real.sin (n * φ) : ℝ) : ℂ) * Complex.I := by
      rw [hεexp, ← Complex.exp_int_mul]
      have : (n : ℂ) * (φ * Complex.I) = ((n * φ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    show (W ((prodSystem D).iter n p)).im
      = Real.sin (n * φ) * (W p).re + Real.cos (n * φ) * (W p).im
    rw [hp, hn]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.mul_im,
      Complex.add_im, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

end Eigen

/-! ### Rectangle integrals and the properties of `f' = Φ_{H₀} a` -/

section Rect

variable (D : Factor S)

omit [StandardBorelSpace S.X] in
theorem memLp_of_bounded_prod {b : S.X × S.X → ℝ} (hb : Measurable b) {C : ℝ}
    (hbb : ∀ p, |b p| ≤ C) (ρ : Measure (S.X × S.X)) [IsFiniteMeasure ρ] : MemLp b 2 ρ :=
  MemLp.of_bound hb.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hbb p)

/-- `L²(λ)` kernel times a bounded tensor is `λ`-integrable. -/
theorem integrable_kernel_tensor {H : S.X × S.X → ℝ} (hH : MemLp H 2 (joining D))
    {u v : S.X → ℝ} (hu : Measurable u) (hv : Measurable v) {Cu Cv : ℝ}
    (hub : ∀ x, |u x| ≤ Cu) (hvb : ∀ x, |v x| ≤ Cv) :
    Integrable (fun p : S.X × S.X => H p * (u p.1 * v p.2)) (joining D) := by
  have hm : Measurable fun p : S.X × S.X => u p.1 * v p.2 :=
    (hu.comp measurable_fst).mul (hv.comp measurable_snd)
  have hb : ∀ p : S.X × S.X, |u p.1 * v p.2| ≤ Cu * Cv := fun p => by
    rw [abs_mul]
    exact mul_le_mul (hub _) (hvb _) (abs_nonneg _) ((abs_nonneg _).trans (hub p.1))
  exact hH.integrable_mul (memLp_of_bounded_prod hm hb _)

/-- Row-by-row form of a rectangle integral. -/
theorem integral_rect_eq {H : S.X × S.X → ℝ} (hH : MemLp H 2 (joining D))
    {u v : S.X → ℝ} (hu : Measurable u) (hv : Measurable v) {Cu Cv : ℝ}
    (hub : ∀ x, |u x| ≤ Cu) (hvb : ∀ x, |v x| ≤ Cv) :
    ∫ p : S.X × S.X, H p * (u p.1 * v p.2) ∂(joining D)
      = ∫ z, u z * condIntegralOp D H v z ∂S.m := by
  rw [← integral_row_eq_joining D (integrable_kernel_tensor D hH hu hv hub hvb)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show ∫ y, H (z, y) * (u z * v y) ∂(condKernel D z)
    = u z * ∫ y, H (z, y) * v y ∂(condKernel D z)
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

/-- The image `Φ_H a` is integrable on the base. -/
theorem integrable_condIntegralOp {H : S.X × S.X → ℝ} (hHm : StronglyMeasurable H)
    (hH : MemLp H 2 (joining D)) {a : S.X → ℝ} (ham : Measurable a) {C : ℝ}
    (hab : ∀ x, |a x| ≤ C) : Integrable (condIntegralOp D H a) S.m := by
  have hF : Integrable (fun p : S.X × S.X => H p * a p.2) (joining D) := by
    have := integrable_kernel_tensor D hH (u := fun _ => (1 : ℝ)) (Cu := 1) measurable_const ham
      (fun _ => by simp) hab
    simpa using this
  rw [← compProd_condKernel_eq_joining D] at hF
  refine Integrable.mono' ((Measure.integrable_compProd_iff hF.aestronglyMeasurable).mp hF).2
    (measurable_condIntegralOp D hHm ham.stronglyMeasurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  unfold condIntegralOp
  exact norm_integral_le_integral_norm _

/-- The eigenvector is orthogonal to tensors: real-kernel form. -/
theorem integral_kernel_tensor_eq_zero (w : Lp ℂ 2 (prodSystem D).m)
    (hperp : ∀ g : Lp ℂ 2 (prodSystem D).m, IsTensorD D g → inner ℂ g w = 0)
    {H₀ H₁ : S.X × S.X → ℝ}
    (hw : w =ᵐ[joining D] fun p => ((H₀ p : ℝ) : ℂ) + ((H₁ p : ℝ) : ℂ) * Complex.I)
    {u v : S.X → ℝ} (hu : Measurable u) (hv : Measurable v) {Cu Cv : ℝ}
    (hub : ∀ x, |u x| ≤ Cu) (hvb : ∀ x, |v x| ≤ Cv)
    (hD : Measurable[D.σ] u ∨ Measurable[D.σ] v) :
    ∫ p : S.X × S.X, H₀ p * (u p.1 * v p.2) ∂(joining D) = 0 := by
  have hm : Measurable fun p : S.X × S.X => u p.1 * v p.2 :=
    (hu.comp measurable_fst).mul (hv.comp measurable_snd)
  have hb : ∀ p : S.X × S.X, |u p.1 * v p.2| ≤ Cu * Cv := fun p => by
    rw [abs_mul]
    exact mul_le_mul (hub _) (hvb _) (abs_nonneg _) ((abs_nonneg _).trans (hub p.1))
  have hmem : MemLp (fun p : S.X × S.X => ((u p.1 * v p.2 : ℝ) : ℂ)) 2 (prodSystem D).m :=
    (memLp_of_bounded_prod hm hb (joining D)).ofReal
  set g : Lp ℂ 2 (prodSystem D).m := hmem.toLp _ with hg
  have hgT : IsTensorD D g :=
    ⟨u, v, hu, hv, ⟨Cu, hub⟩, ⟨Cv, hvb⟩, hD, hmem.coeFn_toLp⟩
  have h0 := hperp g hgT
  rw [L2.inner_def] at h0
  have h1 := congrArg Complex.re h0
  have h2 : ∫ a, (inner ℂ (g a) (w a) : ℂ).re ∂(prodSystem D).m
      = (∫ a, (inner ℂ (g a) (w a) : ℂ) ∂(prodSystem D).m).re :=
    by
      have := integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) g w)
      simpa using this
  rw [← h2] at h1
  simp only [Complex.zero_re] at h1
  rw [← h1]
  refine integral_congr_ae ?_
  filter_upwards [hmem.coeFn_toLp, hw] with p hp1 hp2
  have hp1' : (g p : ℂ) = ((u p.1 * v p.2 : ℝ) : ℂ) := hp1
  rw [hp2]
  simp only [RCLike.inner_apply, hp1']
  simp [Complex.mul_re]

end Rect

/-! ### Kernel data -/

/-- **Kernel data.**  If `D | top` is not a weakly mixing extension, there are a real `φ`
(the eigenvalue of `H = H₀ + i H₁` is `e^{iφ}`, `φ = 2πθ`), strongly measurable kernels
`H₀ H₁ ∈ L²(λ)` rotating by `φ` under `R = T × T`, a measurable `a` with `|a| ≤ 1`, and
`f' = Φ_{H₀} a`, such that `f'` is integrable, not a.e. zero, `m[f'|D] = 0`, and
`f' ∘ Tⁿ = cos(nφ) Φ_{H₀}(a ∘ Tⁿ) - sin(nφ) Φ_{H₁}(a ∘ Tⁿ)` a.e. for every `n : ℤ`.
The last clause is exactly the hypothesis `hf` of `ae_ae_condIntegralOp_orbit` with
`c n = cos (n φ)`, `s n = sin (n φ)`. -/
theorem exists_kernel_data (D : Factor S) (h : ¬ WeaklyMixingExtension D (Factor.top S)) :
    ∃ (φ : ℝ) (H₀ H₁ : S.X × S.X → ℝ) (a f' : S.X → ℝ),
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
          - Real.sin (n * φ) * condIntegralOp D H₁ (fun z => a (S.iter n z)) x := by
  classical
  obtain ⟨f, C, hm, hb, hcond, hncwm⟩ := exists_bounded_of_not_weaklyMixingExtension D h
  obtain ⟨θ, hθ⟩ := exists_atom_of_not_condWeaklyMixing D hm hb hncwm
  obtain ⟨w0, hw0, hwe0, hwperp0⟩ := exists_eigenvector_orthogonal_tensors D hm hb hcond hθ
  have hεn : ‖(fourier 1 θ : ℂ)‖ = 1 := by
    rw [fourier_apply]; exact Circle.norm_coe _
  obtain ⟨w, hwe, hwperp, hwre⟩ := exists_eigenvector_re_ne_zero D (fourier 1 θ)
    ⟨w0, hw0, hwe0, hwperp0⟩
  obtain ⟨φ, H₀, H₁, hH₀, hH₁, hm₀, hm₁, hwH, hrot0, hrot1⟩ :=
    exists_real_kernels D (fourier 1 θ) hεn w hwe
  -- the real part is not a.e. zero
  have hH₀ne : ¬ (H₀ =ᵐ[joining D] 0) := by
    intro hz
    apply hwre
    filter_upwards [hwH, hz] with p h1 h2
    have h2' : H₀ p = 0 := h2
    rw [h1]
    simp [h2']
  -- orthogonality to tensors
  have hperp : ∀ {u v : S.X → ℝ}, Measurable u → Measurable v → ∀ {Cu Cv : ℝ},
      (∀ x, |u x| ≤ Cu) → (∀ x, |v x| ≤ Cv) → (Measurable[D.σ] u ∨ Measurable[D.σ] v) →
      ∫ p : S.X × S.X, H₀ p * (u p.1 * v p.2) ∂(joining D) = 0 :=
    fun hu hv _ _ hub hvb hD => integral_kernel_tensor_eq_zero D w hwperp hwH hu hv hub hvb hD
  -- a bounded `a` with `Φ_{H₀} a ≠ 0`
  have hexB : ∃ B : Set S.X, MeasurableSet B ∧
      ¬ (condIntegralOp D H₀ (B.indicator fun _ => (1 : ℝ)) =ᵐ[S.m] 0) := by
    by_contra hcon
    push Not at hcon
    apply hH₀ne
    refine HilbertSchmidt.ae_eq_zero_of_forall_setIntegral_rectangle_eq_zero (joining D)
      (hm₀.integrable (by norm_num)) ?_
    intro A B hA hB
    have hind : ∫ p in A ×ˢ B, H₀ p ∂(joining D)
        = ∫ p : S.X × S.X, H₀ p * ((A.indicator (fun _ => (1 : ℝ))) p.1 *
            (B.indicator (fun _ => (1 : ℝ))) p.2) ∂(joining D) := by
      rw [← integral_indicator (hA.prod hB)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ B <;> simp [Set.indicator, h1, h2]
    rw [hind, integral_rect_eq D hm₀ (measurable_const.indicator hA)
      (measurable_const.indicator hB) (Cu := 1) (Cv := 1)
      (fun x => by by_cases hx : x ∈ A <;> simp [Set.indicator, hx])
      (fun x => by by_cases hx : x ∈ B <;> simp [Set.indicator, hx])]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hcon B hB] with z hz
    have hz' : condIntegralOp D H₀ (B.indicator fun _ => (1 : ℝ)) z = 0 := hz
    simp [hz']
  obtain ⟨B, hBm, hBne⟩ := hexB
  set a : S.X → ℝ := B.indicator fun _ => (1 : ℝ) with ha
  have ham : Measurable a := measurable_const.indicator hBm
  have hab : ∀ x, |a x| ≤ 1 := fun x => by by_cases hx : x ∈ B <;> simp [ha, hx]
  have hfm : Measurable (condIntegralOp D H₀ a) :=
    measurable_condIntegralOp D hH₀ ham.stronglyMeasurable
  have hfint : Integrable (condIntegralOp D H₀ a) S.m := integrable_condIntegralOp D hH₀ hm₀ ham hab
  refine ⟨φ, H₀, H₁, a, condIntegralOp D H₀ a, hH₀, hH₁, hm₀, hm₁, hrot0, hrot1, ham, hab, rfl,
    hfm, hfint, hBne, ?_, ?_⟩
  · -- `m[f'|D] = 0`
    symm
    refine ae_eq_condExp_of_forall_setIntegral_eq D.le hfint (fun s _ _ => integrableOn_zero) ?_
      (aestronglyMeasurable_zero)
    intro Z hZ _
    have hZm : MeasurableSet Z := D.le _ hZ
    simp only [Pi.zero_apply, integral_zero]
    rw [← integral_indicator hZm]
    have h1 := hperp (u := Z.indicator fun _ => (1 : ℝ)) (v := a)
      (measurable_const.indicator hZm) ham (Cu := 1) (Cv := 1)
      (fun x => by by_cases hx : x ∈ Z <;> simp [Set.indicator, hx]) hab
      (Or.inl (by
        letI := D.σ
        exact measurable_const.indicator hZ))
    rw [integral_rect_eq D hm₀ (measurable_const.indicator hZm) ham (Cu := 1) (Cv := 1)
      (fun x => by by_cases hx : x ∈ Z <;> simp [Set.indicator, hx]) hab] at h1
    refine h1.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
    by_cases hz : z ∈ Z <;> simp [Set.indicator, hz]
  · intro n
    have han : Measurable fun z => a (S.iter n z) := ham.comp (S.measurable_iter n)
    have hanb : ∀ z, |a (S.iter n z)| ≤ 1 := fun z => hab _
    have e1 := condIntegralOp_comp_iter D hH₀ hm₀ ham.stronglyMeasurable hab n
    have e2 := condIntegralOp_congr_ae_kernel D (hrot0 n) (fun y => a (S.iter n y))
    have e3 := condIntegralOp_comb_ae D hH₀ hH₁ hm₀ hm₁ han hanb (Real.cos (n * φ))
      (Real.sin (n * φ))
    filter_upwards [e1, e2, e3] with x h1 h2 h3
    exact (h1.trans h2).trans h3

end CantorSzemeredi.Proof

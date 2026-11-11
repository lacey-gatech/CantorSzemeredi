module

public import CantorSzemeredi.Port.Dynamics.Localize
public import CantorSzemeredi.Port.Dynamics.Extensions
public import CantorSzemeredi.Port.Dynamics.CompactSystem
public import CantorSzemeredi.Proof.Dichotomy.Defs
public import Mathlib

/-!
# Dichotomy: truncation

`not_weaklyMixingExtension_top` : if `D | top` is not a weakly mixing extension, there is a
bounded measurable `f` (`|f| ≤ C` everywhere) with `E(f|D) = 0` almost everywhere that is not
conditionally weakly mixing.  This is the form consumed by
`CSZPort.MPS.exists_atom_of_not_condWeaklyMixing`.

Proof by truncation: for `f` in the Hilbert module with `E(f|D) = 0`, the functions
`f_K = clamp_K f - E(clamp_K f | D)` are bounded, have `E(f_K|D) = 0`, and
`‖f_K - f‖_{L²(D)}`-norm tends to `0` in `L²`; the Cesàro averages of `|⟨Tⁿ f, f⟩|` are then
controlled by those of `f_K` up to `4 C₁ ‖‖f_K - f‖_cond‖_{L²}`.
-/

@[expose] public section

namespace CantorSzemeredi.Proof

open MeasureTheory CSZPort CSZPort.MPS Filter Topology

variable {S : MPS}

/-! ### Elementary facts on `condInner` and `condNorm` -/

theorem condInner_congr_ae (D : Factor S) {f f' g g' : S.X → ℝ} (hf : f =ᵐ[S.m] f')
    (hg : g =ᵐ[S.m] g') : condInner D f g =ᵐ[S.m] condInner D f' g' :=
  condExp_congr_ae (hf.mul hg)

theorem condNorm_neg (D : Factor S) (u : S.X → ℝ) : condNorm D (-u) = condNorm D u := by
  funext x
  simp [condNorm, condInner]

theorem aestronglyMeasurable_condInner (D : Factor S) (f g : S.X → ℝ) :
    AEStronglyMeasurable (condInner D f g) S.m :=
  (stronglyMeasurable_condExp.mono D.le).aestronglyMeasurable

theorem aestronglyMeasurable_condNorm (D : Factor S) (f : S.X → ℝ) :
    AEStronglyMeasurable (condNorm D f) S.m :=
  Real.continuous_sqrt.comp_aestronglyMeasurable (aestronglyMeasurable_condInner D f f)

/-- Conditional weak mixing only depends on the a.e. class. -/
theorem condWeaklyMixing_congr (D : Factor S) {f g : S.X → ℝ} (h : f =ᵐ[S.m] g)
    (hf : CondWeaklyMixing D f) : CondWeaklyMixing D g := by
  unfold CondWeaklyMixing at hf ⊢
  refine hf.congr fun N => eLpNorm_congr_ae ?_
  have hn : ∀ n : ℕ, condInner D (f ∘ S.T^[n]) f =ᵐ[S.m] condInner D (g ∘ S.T^[n]) g :=
    fun n => condInner_congr_ae D
      ((S.measurePreserving_T_iterate n).quasiMeasurePreserving.ae_eq_comp h) h
  have hall : ∀ᵐ x ∂S.m, ∀ n : ℕ, condInner D (f ∘ S.T^[n]) f x = condInner D (g ∘ S.T^[n]) g x :=
    ae_all_iff.2 hn
  filter_upwards [hall] with x hx
  simp only [hx]

/-! ### The Cesàro comparison -/

/-- The average of functions each of `L²`-norm at most `c` has `L²`-norm at most `c`. -/
theorem eLpNorm_avg_le {μ : Measure S.X} (h : ℕ → S.X → ℝ)
    (c : ENNReal) (hc : ∀ n, eLpNorm (h n) 2 μ ≤ c)
    (N : ℕ) :
    eLpNorm (fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, h n x) 2 μ ≤ c := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h1 : (fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, h n x)
      = (N : ℝ)⁻¹ • (∑ n ∈ Finset.range N, h n) := by
    funext x; simp [Finset.sum_apply]
  rw [h1, eLpNorm_const_smul]
  have h2 := eLpNorm_sum_le (μ := μ) (s := Finset.range N) (f := h) (p := 2)
    (by norm_num)
  have h3 : ∑ n ∈ Finset.range N, eLpNorm (h n) 2 μ ≤ N * c := by
    calc ∑ n ∈ Finset.range N, eLpNorm (h n) 2 μ ≤ ∑ _n ∈ Finset.range N, c :=
          Finset.sum_le_sum fun n _ => hc n
      _ = N * c := by simp
  calc ‖(N : ℝ)⁻¹‖ₑ * eLpNorm (∑ n ∈ Finset.range N, h n) 2 μ
      ≤ ‖(N : ℝ)⁻¹‖ₑ * (N * c) := by gcongr; exact h2.trans h3
    _ = c := by
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      rw [← mul_assoc]
      have : ‖(N : ℝ)⁻¹‖ₑ * (N : ENNReal) = 1 := by
        rw [enorm_inv hN0, ← ofReal_norm]
        simp only [Real.norm_natCast]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        simp [hN0]
      rw [this, one_mul]

/-- Pointwise comparison of one correlation: with `δ = ‖v - f‖_cond`,
`|⟨Tⁿ f, f⟩| ≤ |⟨Tⁿ v, v⟩| + 3 C₁ δ(Tⁿ x) + C₁ δ(x)` almost everywhere. -/
theorem abs_condInner_iterate_le (D : Factor S) {f v : S.X → ℝ} (hf : MemLp f 2 S.m)
    (hv : MemLp v 2 S.m) {C₁ : ℝ} (hC : ∀ᵐ x ∂S.m, condNorm D f x ≤ C₁)
    (hδ : ∀ᵐ x ∂S.m, condNorm D (v - f) x ≤ 2 * C₁) (n : ℕ) :
    ∀ᵐ x ∂S.m, |condInner D (f ∘ S.T^[n]) f x| ≤ |condInner D (v ∘ S.T^[n]) v x|
      + 3 * C₁ * condNorm D (v - f) (S.T^[n] x) + C₁ * condNorm D (v - f) x := by
  have hTn := S.measurePreserving_T_iterate n
  have hw : MemLp (v - f) 2 S.m := hv.sub hf
  have hfn : MemLp (f ∘ S.T^[n]) 2 S.m := hf.comp_measurePreserving hTn
  have hvn : MemLp (v ∘ S.T^[n]) 2 S.m := hv.comp_measurePreserving hTn
  have hwn : MemLp ((v - f) ∘ S.T^[n]) 2 S.m := hw.comp_measurePreserving hTn
  have hI : ∀ {a b : S.X → ℝ}, MemLp a 2 S.m → MemLp b 2 S.m → Integrable (a * b) S.m :=
    fun ha hb => ha.integrable_mul hb
  -- the algebraic identity
  have hid : (v ∘ S.T^[n]) * v - (f ∘ S.T^[n]) * f
      = ((v - f) ∘ S.T^[n]) * v + (f ∘ S.T^[n]) * (v - f) := by
    funext x; simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Function.comp_apply]; ring
  have hlin : condInner D (v ∘ S.T^[n]) v - condInner D (f ∘ S.T^[n]) f
      =ᵐ[S.m] condInner D ((v - f) ∘ S.T^[n]) v + condInner D (f ∘ S.T^[n]) (v - f) := by
    have h1 := condExp_sub (hI hvn hv) (hI hfn hf) D.σ
    have h2 := condExp_add (hI hwn hv) (hI hfn hw) D.σ
    unfold condInner
    rw [← hid] at h2
    filter_upwards [h1, h2] with x h1x h2x
    simp only [Pi.sub_apply, Pi.add_apply] at h1x h2x ⊢
    rw [← h1x, h2x]
  have hcs1 := abs_condInner_le D (hwn.integrable_mul hwn) (hv.integrable_mul hv)
    (hI hwn hv)
  have hcs2 := abs_condInner_le D (hfn.integrable_mul hfn) (hw.integrable_mul hw)
    (hI hfn hw)
  have hshiftw := condNorm_comp_iterate D n hw
  have hshiftf := condNorm_comp_iterate D n hf
  have htri : ∀ᵐ x ∂S.m, condNorm D (f + (v - f)) x ≤ condNorm D f x + condNorm D (v - f) x :=
    condNorm_add_le D hf hw
  have hC' : ∀ᵐ x ∂S.m, condNorm D f (S.T^[n] x) ≤ C₁ :=
    hTn.quasiMeasurePreserving.ae hC
  have hδ' : ∀ᵐ x ∂S.m, condNorm D (v - f) (S.T^[n] x) ≤ 2 * C₁ :=
    hTn.quasiMeasurePreserving.ae hδ
  have hvf : f + (v - f) = v := by funext x; simp
  rw [hvf] at htri
  filter_upwards [hlin, hcs1, hcs2, hshiftw, hshiftf, htri, hC, hC', hδ, hδ'] with
    x hl h1 h2 sw sf ht hCx hCx' hδx hδx'
  have n1 := condNorm_nonneg D (v - f) x
  have n2 := condNorm_nonneg D (v - f) (S.T^[n] x)
  have n3 := condNorm_nonneg D f x
  have n4 := condNorm_nonneg D v x
  have hC0 : 0 ≤ C₁ := n3.trans hCx
  simp only [Function.comp_apply] at sw sf
  rw [sw] at h1
  rw [sf] at h2
  have e1 : |condInner D ((v - f) ∘ S.T^[n]) v x| ≤ 3 * C₁ * condNorm D (v - f) (S.T^[n] x) := by
    refine h1.trans ?_
    have : condNorm D v x ≤ 3 * C₁ := by linarith
    calc condNorm D (v - f) (S.T^[n] x) * condNorm D v x
        ≤ condNorm D (v - f) (S.T^[n] x) * (3 * C₁) := by gcongr
      _ = _ := by ring
  have e2 : |condInner D (f ∘ S.T^[n]) (v - f) x| ≤ C₁ * condNorm D (v - f) x := by
    refine h2.trans ?_
    gcongr
  have : condInner D (f ∘ S.T^[n]) f x
      = condInner D (v ∘ S.T^[n]) v x - (condInner D ((v - f) ∘ S.T^[n]) v x
        + condInner D (f ∘ S.T^[n]) (v - f) x) := by
    simp only [Pi.sub_apply, Pi.add_apply] at hl
    linarith
  rw [this]
  calc _ ≤ |condInner D (v ∘ S.T^[n]) v x| + |condInner D ((v - f) ∘ S.T^[n]) v x
        + condInner D (f ∘ S.T^[n]) (v - f) x| := abs_sub _ _
    _ ≤ _ := by
      have := abs_add_le (condInner D ((v - f) ∘ S.T^[n]) v x)
        (condInner D (f ∘ S.T^[n]) (v - f) x)
      linarith

/-- **Cesàro comparison.** -/
theorem eLpNorm_cesaro_le (D : Factor S) {f v : S.X → ℝ} (hf : MemLp f 2 S.m)
    (hv : MemLp v 2 S.m) {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hC : ∀ᵐ x ∂S.m, condNorm D f x ≤ C₁)
    (hδ : ∀ᵐ x ∂S.m, condNorm D (v - f) x ≤ 2 * C₁) (N : ℕ) :
    eLpNorm (fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, |condInner D (f ∘ S.T^[n]) f x|) 2 S.m
      ≤ eLpNorm (fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          |condInner D (v ∘ S.T^[n]) v x|) 2 S.m
        + ENNReal.ofReal (4 * C₁) * eLpNorm (condNorm D (v - f)) 2 S.m := by
  set δ := condNorm D (v - f) with hδdef
  have hδm : AEStronglyMeasurable δ S.m := aestronglyMeasurable_condNorm D _
  have hTm : ∀ n : ℕ, MeasurePreserving (S.T^[n]) S.m S.m := S.measurePreserving_T_iterate
  set Av : S.X → ℝ := fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
    |condInner D (v ∘ S.T^[n]) v x| with hAv
  set h : ℕ → S.X → ℝ := fun n x => 3 * C₁ * δ (S.T^[n] x) + C₁ * δ x with hh
  set R : S.X → ℝ := fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, h n x with hR
  have hRle : eLpNorm R 2 S.m ≤ ENNReal.ofReal (4 * C₁) * eLpNorm δ 2 S.m := by
    refine eLpNorm_avg_le h _ ?_ N
    intro n
    have hdn : AEStronglyMeasurable (δ ∘ S.T^[n]) S.m :=
      hδm.comp_quasiMeasurePreserving (hTm n).quasiMeasurePreserving
    have hnorm : eLpNorm (δ ∘ S.T^[n]) 2 S.m = eLpNorm δ 2 S.m :=
      eLpNorm_comp_measurePreserving hδm (hTm n)
    have hsplit : h n = (3 * C₁) • (δ ∘ S.T^[n]) + C₁ • δ := by
      funext x; simp [hh, smul_eq_mul]
    have hn1 : eLpNorm ((3 * C₁) • (δ ∘ S.T^[n])) 2 S.m
        = ENNReal.ofReal (3 * C₁) * eLpNorm δ 2 S.m := by
      rw [eLpNorm_const_smul, hnorm, ← ofReal_norm, Real.norm_of_nonneg (by positivity)]
    have hn2 : eLpNorm (C₁ • δ) 2 S.m = ENNReal.ofReal C₁ * eLpNorm δ 2 S.m := by
      rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_of_nonneg hC₁]
    calc eLpNorm (h n) 2 S.m
        ≤ eLpNorm ((3 * C₁) • (δ ∘ S.T^[n])) 2 S.m + eLpNorm (C₁ • δ) 2 S.m := by
          rw [hsplit]; exact eLpNorm_add_le (by norm_num)
      _ = ENNReal.ofReal (4 * C₁) * eLpNorm δ 2 S.m := by
          rw [hn1, hn2, ← add_mul, ← ENNReal.ofReal_add (by positivity) hC₁]
          ring_nf
  have hall : ∀ᵐ x ∂S.m, ∀ n : ℕ, |condInner D (f ∘ S.T^[n]) f x| ≤
      |condInner D (v ∘ S.T^[n]) v x| + h n x :=
    ae_all_iff.2 fun n => by
      filter_upwards [abs_condInner_iterate_le D hf hv hC hδ n] with x hx
      simp only [hh]; linarith
  have hmono : eLpNorm (fun x => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      |condInner D (f ∘ S.T^[n]) f x|) 2 S.m ≤ eLpNorm (Av + R) 2 S.m := by
    refine eLpNorm_mono_ae ?_ ?_
    · exact AEStronglyMeasurable.const_mul
        (Finset.aestronglyMeasurable_fun_sum _ fun n _ =>
          (aestronglyMeasurable_condInner D _ _).norm) _
    filter_upwards [hall] with x hx
    have hs : ∑ n ∈ Finset.range N, |condInner D (f ∘ S.T^[n]) f x|
        ≤ ∑ n ∈ Finset.range N, (|condInner D (v ∘ S.T^[n]) v x| + h n x) :=
      Finset.sum_le_sum fun n _ => hx n
    rw [Finset.sum_add_distrib] at hs
    have hNpos : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    have hnn : 0 ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, |condInner D (f ∘ S.T^[n]) f x| :=
      mul_nonneg hNpos (Finset.sum_nonneg fun n _ => abs_nonneg _)
    have hAvnn : 0 ≤ Av x := mul_nonneg hNpos (Finset.sum_nonneg fun n _ => abs_nonneg _)
    have hRnn : 0 ≤ R x := by
      refine mul_nonneg hNpos (Finset.sum_nonneg fun n _ => ?_)
      simp only [hh]
      have := condNorm_nonneg D (v - f) (S.T^[n] x)
      have := condNorm_nonneg D (v - f) x
      positivity
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (add_nonneg hAvnn hRnn)]
    simp only [hAv, hR]
    rw [← mul_add]
    rw [Real.norm_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left hs hNpos
  calc _ ≤ eLpNorm (Av + R) 2 S.m := hmono
    _ ≤ eLpNorm Av 2 S.m + eLpNorm R 2 S.m := eLpNorm_add_le (by norm_num)
    _ ≤ _ := by gcongr

/-- Approximation criterion for conditional weak mixing. -/
theorem condWeaklyMixing_of_approx (D : Factor S) {f : S.X → ℝ} (hf : MemLp f 2 S.m) {C₁ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC : ∀ᵐ x ∂S.m, condNorm D f x ≤ C₁)
    (happrox : ∀ b : ENNReal, 0 < b → ∃ v : S.X → ℝ, MemLp v 2 S.m ∧ CondWeaklyMixing D v ∧
      (∀ᵐ x ∂S.m, condNorm D (v - f) x ≤ 2 * C₁) ∧
      ENNReal.ofReal (4 * C₁) * eLpNorm (condNorm D (v - f)) 2 S.m < b) :
    CondWeaklyMixing D f := by
  unfold CondWeaklyMixing
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨v, hv, hvm, hδ, hsmall⟩ := happrox (ε / 2) (ENNReal.half_pos hε.ne')
  have hev := ENNReal.tendsto_nhds_zero.1 hvm (ε / 2) (ENNReal.half_pos hε.ne')
  filter_upwards [hev] with N hN
  calc _ ≤ _ := eLpNorm_cesaro_le D hf hv hC₁ hC hδ N
    _ ≤ ε / 2 + ε / 2 := add_le_add hN hsmall.le
    _ = ε := ENNReal.add_halves ε

/-! ### Truncation -/

theorem eLpNorm_two_eq_sqrt_integral {g : S.X → ℝ} (hg : MemLp g 2 S.m) :
    eLpNorm g 2 S.m = ENNReal.ofReal (Real.sqrt (∫ x, g x ^ 2 ∂S.m)) := by
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp [Real.sqrt_eq_rpow, Real.norm_eq_abs]

theorem clamp_facts (K t : ℝ) (hK : 0 ≤ K) :
    |t - max (-K) (min K t)| ≤ |t| ∧ |max (-K) (min K t)| ≤ K ∧
    (|t| ≤ K → max (-K) (min K t) = t) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_le]
    rcases le_total t 0 with h | h
    · rw [abs_of_nonpos h]; constructor <;> (simp only [max_def, min_def]; split_ifs <;> linarith)
    · rw [abs_of_nonneg h]; constructor <;> (simp only [max_def, min_def]; split_ifs <;> linarith)
  · rw [abs_le]; constructor <;> (simp only [max_def, min_def]; split_ifs <;> linarith)
  · intro h
    rw [abs_le] at h
    simp only [max_def, min_def]; split_ifs <;> linarith

/-- Clamping to `[-K, K]`. -/
def clampFn (K : ℝ) (f : S.X → ℝ) : S.X → ℝ := fun y => max (-K) (min K (f y))

theorem measurable_clampFn {K : ℝ} {f : S.X → ℝ} (hf : Measurable f) :
    Measurable (clampFn K f) :=
  measurable_const.max (measurable_const.min hf)

section Trunc

variable (D : Factor S) {f : S.X → ℝ}

theorem memLp_sub_clampFn (hf : MemLp f 2 S.m) (hfm : Measurable f) {K : ℝ} (hK : 0 ≤ K) :
    MemLp (f - clampFn K f) 2 S.m :=
  hf.sub (memLp_two_of_bounded (measurable_clampFn hfm) fun x => (clamp_facts K (f x) hK).2.1)

theorem condNorm_sub_clampFn_le (hf : MemLp f 2 S.m) (hfm : Measurable f) {K : ℝ}
    (hK : 0 ≤ K) : ∀ᵐ x ∂S.m, condNorm D (f - clampFn K f) x ≤ condNorm D f x := by
  have he := memLp_sub_clampFn hf hfm hK
  have hmono : condInner D (f - clampFn K f) (f - clampFn K f) ≤ᵐ[S.m] condInner D f f := by
    refine condExp_mono (he.integrable_mul he) (hf.integrable_mul hf) ?_
    filter_upwards with x
    have h1 := (clamp_facts K (f x) hK).1
    simp only [Pi.mul_apply, Pi.sub_apply, clampFn]
    nlinarith [abs_nonneg (f x - max (-K) (min K (f x))), sq_abs (f x),
      sq_abs (f x - max (-K) (min K (f x))), mul_self_le_mul_self (abs_nonneg _) h1]
  filter_upwards [hmono] with x hx
  exact Real.sqrt_le_sqrt hx

theorem tendsto_eLpNorm_condNorm_sub_clampFn (hf : MemLp f 2 S.m) (hfm : Measurable f) :
    Tendsto (fun K : ℕ => eLpNorm (condNorm D (f - clampFn (K : ℝ) f)) 2 S.m) atTop (𝓝 0) := by
  have hK : ∀ K : ℕ, (0 : ℝ) ≤ K := fun K => Nat.cast_nonneg K
  have hmem : ∀ K : ℕ, MemLp (condNorm D (f - clampFn (K : ℝ) f)) 2 S.m := by
    intro K
    have he := memLp_sub_clampFn hf hfm (hK K)
    rw [memLp_two_iff_integrable_sq (aestronglyMeasurable_condNorm D _)]
    have h1 := condNorm_sq D (f - clampFn (K : ℝ) f)
    refine (integrable_condExp (m := D.σ) (f := (f - clampFn (K : ℝ) f) *
      (f - clampFn (K : ℝ) f))).congr ?_
    filter_upwards [h1] with x hx
    exact hx.symm
  have hint : ∀ K : ℕ, ∫ x, condNorm D (f - clampFn (K : ℝ) f) x ^ 2 ∂S.m
      = ∫ x, (f x - clampFn (K : ℝ) f x) ^ 2 ∂S.m := by
    intro K
    have he := memLp_sub_clampFn hf hfm (hK K)
    rw [integral_congr_ae (condNorm_sq D _)]
    unfold condInner
    rw [integral_condExp D.le]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [sq]
  have hlim : Tendsto (fun K : ℕ => ∫ x, (f x - clampFn (K : ℝ) f x) ^ 2 ∂S.m) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := S.m)
      (F := fun (K : ℕ) x => (f x - clampFn (K : ℝ) f x) ^ 2) (f := fun _ => (0 : ℝ))
      (bound := fun x => f x ^ 2)
      (fun K => ((hfm.sub (measurable_clampFn hfm)).pow_const 2).aestronglyMeasurable)
      hf.integrable_sq
      (fun K => Filter.Eventually.of_forall fun x => by
        have h1 := (clamp_facts (K : ℝ) (f x) (hK K)).1
        rw [Real.norm_eq_abs, abs_pow, ← sq_abs (f x)]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2)
      (Filter.Eventually.of_forall fun x => by
        refine tendsto_const_nhds.congr' ?_
        obtain ⟨K₀, hK₀⟩ := exists_nat_ge |f x|
        filter_upwards [eventually_ge_atTop K₀] with K hKK
        have : |f x| ≤ (K : ℝ) := hK₀.trans (by exact_mod_cast hKK)
        simp [clampFn, (clamp_facts (K : ℝ) (f x) (hK K)).2.2 this])
    simpa using this
  have h2 : Tendsto (fun K : ℕ => ENNReal.ofReal (Real.sqrt
      (∫ x, condNorm D (f - clampFn (K : ℝ) f) x ^ 2 ∂S.m))) atTop (𝓝 0) := by
    simp only [hint]
    have h3 : Tendsto (fun K : ℕ => Real.sqrt
        (∫ x, (f x - clampFn (K : ℝ) f x) ^ 2 ∂S.m)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hlim
      rwa [Real.sqrt_zero] at this
    have h4 := (ENNReal.continuous_ofReal.tendsto 0).comp h3
    rwa [ENNReal.ofReal_zero] at h4
  refine h2.congr fun K => ?_
  exact (eLpNorm_two_eq_sqrt_integral (hmem K)).symm

/-- One truncation step: a bounded measurable `v` with `E(v|D) = 0` whose distance to `f`
in the conditional norm is at most twice that of `f` to its clamp. -/
theorem exists_truncation_step (hf : MemLp f 2 S.m) (hfm : Measurable f)
    (hf0 : S.m[f|D.σ] =ᵐ[S.m] 0) {K : ℝ} (hK : 0 ≤ K) :
    ∃ v : S.X → ℝ, Measurable v ∧ (∀ x, |v x| ≤ 2 * K) ∧ (S.m[v|D.σ] =ᵐ[S.m] 0) ∧
      ∀ᵐ x ∂S.m, condNorm D (v - f) x ≤ 2 * condNorm D (f - clampFn K f) x := by
  set φ := clampFn K f with hφ
  have hφm : Measurable φ := measurable_clampFn hfm
  have hφb : ∀ x, |φ x| ≤ K := fun x => (clamp_facts K (f x) hK).2.1
  have hφL : MemLp φ 2 S.m := memLp_two_of_bounded hφm hφb
  set e := f - φ with he
  have heL : MemLp e 2 S.m := hf.sub hφL
  set g : S.X → ℝ := fun x => max (-K) (min K ((S.m[φ|D.σ]) x)) with hg
  have hgD : StronglyMeasurable[D.σ] g :=
    (continuous_const.max (continuous_const.min continuous_id)).comp_stronglyMeasurable
      stronglyMeasurable_condExp
  have hgm : Measurable g := (hgD.mono D.le).measurable
  have hgb : ∀ x, |g x| ≤ K := fun x => (clamp_facts K _ hK).2.1
  have hgL : MemLp g 2 S.m := memLp_two_of_bounded hgm hgb
  have hgae : g =ᵐ[S.m] S.m[φ|D.σ] := by
    have hb : ∀ᵐ x ∂S.m, |(S.m[φ|D.σ]) x| ≤ K :=
      ae_bdd_abs_condExp_of_ae_bdd_abs (Filter.Eventually.of_forall hφb)
    filter_upwards [hb] with x hx
    exact (clamp_facts K _ hK).2.2 hx
  refine ⟨φ - g, hφm.sub hgm, fun x => ?_, ?_, ?_⟩
  · have := abs_sub (φ x) (g x)
    simp only [Pi.sub_apply]
    linarith [hφb x, hgb x]
  · have h1 := condExp_sub (hφL.integrable one_le_two) (hgL.integrable one_le_two) D.σ
    have h2 : S.m[g|D.σ] = g := condExp_of_stronglyMeasurable D.le hgD (hgL.integrable one_le_two)
    filter_upwards [h1, hgae] with x hx hgx
    simp only [Pi.sub_apply, Pi.zero_apply] at hx ⊢
    rw [hx, h2, hgx]; ring
  · -- `v - f = (-e) + (-g)`
    have hsplit : (φ - g) - f = (-e) + (-g) := by funext x; simp [he]; ring
    have hnegeL : MemLp (-e) 2 S.m := heL.neg
    have hneggL : MemLp (-g) 2 S.m := hgL.neg
    have htri := condNorm_add_le D hnegeL hneggL
    rw [← hsplit] at htri
    rw [condNorm_neg, condNorm_neg] at htri
    -- `condNorm g = |g|`
    have hgg : condInner D g g = g * g :=
      condExp_of_stronglyMeasurable D.le (hgD.mul hgD) (hgL.integrable_mul hgL)
    have hgn : ∀ x, condNorm D g x = |g x| := fun x => by
      simp only [condNorm, hgg, Pi.mul_apply, Real.sqrt_mul_self_eq_abs]
    -- `|g| ≤ condNorm e`
    have hphi : S.m[φ|D.σ] =ᵐ[S.m] -(S.m[e|D.σ]) := by
      have hfe : φ = f - e := by funext x; simp [he]
      have h1 := condExp_sub (hf.integrable one_le_two) (heL.integrable one_le_two) D.σ
      rw [hfe]
      filter_upwards [h1, hf0] with x hx hf0x
      simp only [Pi.sub_apply, Pi.zero_apply, Pi.neg_apply] at hx hf0x ⊢
      rw [hx, hf0x]; ring
    have h1mem : MemLp (1 : S.X → ℝ) 2 S.m := memLp_const 1
    have hcs := abs_condInner_le D (heL.integrable_mul heL) (h1mem.integrable_mul h1mem)
      (heL.integrable_mul h1mem)
    have hone : condNorm D 1 = fun _ => 1 := by
      funext x
      have : (1 : S.X → ℝ) * 1 = fun _ => (1 : ℝ) := by funext y; simp
      simp only [condNorm, condInner, this, condExp_const D.le, Real.sqrt_one]
    have hee : condInner D e 1 = S.m[e|D.σ] := by
      rw [condInner, mul_one]
    filter_upwards [htri, hcs, hgae, hphi] with x ht hc hgx hpx
    rw [hee, hone] at hc
    have : |g x| ≤ condNorm D e x := by
      rw [hgx, hpx]
      simpa [abs_neg] using hc
    rw [hgn] at ht
    have h' : condNorm D (φ - g - f) x ≤ condNorm D e x + |g x| := ht
    show condNorm D (φ - g - f) x ≤ 2 * condNorm D e x
    linarith

/-- **Truncation.**  For `f ∈ L²` measurable with `E(f|D) = 0`, there are bounded measurable
`v K` with `E(v K|D) = 0` converging to `f` in the `L²` norm of the conditional norm. -/
theorem exists_truncation (hf : MemLp f 2 S.m) (hfm : Measurable f)
    (hf0 : S.m[f|D.σ] =ᵐ[S.m] 0) :
    ∃ v : ℕ → S.X → ℝ, (∀ K, Measurable (v K)) ∧ (∀ K, ∃ B : ℝ, ∀ x, |v K x| ≤ B) ∧
      (∀ K, S.m[v K|D.σ] =ᵐ[S.m] 0) ∧
      (∀ K, ∀ᵐ x ∂S.m, condNorm D (v K - f) x ≤ 2 * condNorm D f x) ∧
      Tendsto (fun K => eLpNorm (condNorm D (v K - f)) 2 S.m) atTop (𝓝 0) := by
  have hK : ∀ K : ℕ, (0 : ℝ) ≤ K := fun K => Nat.cast_nonneg K
  choose v hvm hvb hv0 hvn using fun K : ℕ => exists_truncation_step D hf hfm hf0 (hK K)
  refine ⟨v, hvm, fun K => ⟨2 * K, hvb K⟩, hv0, fun K => ?_, ?_⟩
  · filter_upwards [hvn K, condNorm_sub_clampFn_le D hf hfm (hK K)] with x h1 h2
    linarith
  · have h0 := tendsto_eLpNorm_condNorm_sub_clampFn D hf hfm
    have h1 : Tendsto (fun K : ℕ => ENNReal.ofReal 2 *
        eLpNorm (condNorm D (f - clampFn (K : ℝ) f)) 2 S.m) atTop (𝓝 0) := by
      rw [← mul_zero (ENNReal.ofReal 2)]
      exact ENNReal.Tendsto.const_mul h0 (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
      (fun K => bot_le) fun K => ?_
    have hmem := memLp_sub_clampFn hf hfm (hK K)
    calc eLpNorm (condNorm D (v K - f)) 2 S.m
        ≤ eLpNorm (fun x => (2 : ℝ) * condNorm D (f - clampFn (K : ℝ) f) x) 2 S.m := by
          refine eLpNorm_mono_ae ?_ ?_
          · exact aestronglyMeasurable_condNorm D _
          · filter_upwards [hvn K] with x hx
            rw [Real.norm_of_nonneg (condNorm_nonneg D _ _),
              Real.norm_of_nonneg (by have := condNorm_nonneg D (f - clampFn (K : ℝ) f) x; positivity)]
            exact hx
      _ = ENNReal.ofReal 2 * eLpNorm (condNorm D (f - clampFn (K : ℝ) f)) 2 S.m := by
          have : (fun x => (2 : ℝ) * condNorm D (f - clampFn (K : ℝ) f) x)
              = (2 : ℝ) • condNorm D (f - clampFn (K : ℝ) f) := by
            funext x; simp [smul_eq_mul]
          rw [this, eLpNorm_const_smul, ← ofReal_norm, Real.norm_of_nonneg (by norm_num)]

end Trunc

/-- If `D | top` is not a weakly mixing extension, there is
a bounded measurable `f` (`|f| ≤ C` everywhere) with `E(f|D) = 0` almost everywhere that is not
conditionally weakly mixing.  The conclusion matches the hypotheses of
`CSZPort.MPS.exists_atom_of_not_condWeaklyMixing` (`Measurable f`, `∀ x, |f x| ≤ C`,
`¬ CondWeaklyMixing D f`). -/
theorem exists_bounded_of_not_weaklyMixingExtension (D : Factor S)
    (h : ¬ WeaklyMixingExtension D (Factor.top S)) :
    ∃ (f : S.X → ℝ) (C : ℝ), Measurable f ∧ (∀ x, |f x| ≤ C) ∧
      (S.m[f|D.σ] =ᵐ[S.m] 0) ∧ ¬ CondWeaklyMixing D f := by
  by_contra hcon
  push Not at hcon
  apply h
  intro f0 hmod hf00
  set f := hmod.meas.mk f0 with hfdef
  have hfm : Measurable f := by
    have := hmod.meas.stronglyMeasurable_mk
    exact this.measurable
  have hae : f0 =ᵐ[S.m] f := hmod.meas.ae_eq_mk
  have hfL : MemLp f 2 S.m := hmod.memLp.ae_eq hae
  have hf0 : S.m[f|D.σ] =ᵐ[S.m] 0 := (condExp_congr_ae hae.symm).trans hf00
  obtain ⟨C, hC⟩ := hmod.bddCondNorm
  have hnorm : condNorm D f =ᵐ[S.m] condNorm D f0 := by
    filter_upwards [condInner_congr_ae D hae.symm hae.symm] with x hx
    simp only [condNorm, hx]
  set C₁ := max C 0 with hC₁def
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  have hCf : ∀ᵐ x ∂S.m, condNorm D f x ≤ C₁ := by
    filter_upwards [hnorm, hC] with x h1 h2
    rw [h1]; exact h2.trans (le_max_left _ _)
  obtain ⟨v, hvm, hvb, hv0, hvn, hvt⟩ := exists_truncation D hfL hfm hf0
  have hcw : CondWeaklyMixing D f := by
    refine condWeaklyMixing_of_approx D hfL hC₁ hCf fun b hb => ?_
    have h1 : Tendsto (fun K => ENNReal.ofReal (4 * C₁) *
        eLpNorm (condNorm D (v K - f)) 2 S.m) atTop (𝓝 0) := by
      rw [← mul_zero (ENNReal.ofReal (4 * C₁))]
      exact ENNReal.Tendsto.const_mul hvt (Or.inr ENNReal.ofReal_ne_top)
    obtain ⟨K, hK⟩ := (h1.eventually (gt_mem_nhds hb)).exists
    obtain ⟨B, hB⟩ := hvb K
    refine ⟨v K, memLp_two_of_bounded (hvm K) hB, hcon (v K) B (hvm K) hB (hv0 K), ?_, hK⟩
    filter_upwards [hvn K, hCf] with x h1 h2
    linarith
  exact condWeaklyMixing_congr D hae.symm hcw

end CantorSzemeredi.Proof

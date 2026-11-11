module

public import CantorSzemeredi.Proof.Dichotomy.Defs
public import CantorSzemeredi.Proof.Dichotomy.FibreConst
public import Mathlib

/-!
# The class 𝔄 is a lattice algebra

`compactClass D` (the class 𝔄 of bounded measurable conditionally compact functions, see `Defs`)
is closed under the operations needed by the σ-algebra of compact sets (`Sigma.lean`):

* `compactClass_lipschitz` : `f ∈ 𝔄 → φ ∘ f ∈ 𝔄` for every Lipschitz `φ : ℝ → ℝ`.  This is
  the single lemma behind `+`-free operations; `compactClass_smul`, `compactClass_abs`,
  `compactClass_clamp`, `compactClass_const_add` are specialisations.
* `compactClass_add`, `compactClass_mul`, `compactClass_max`, `compactClass_min`;
* `compactClass_comp_T`, `compactClass_comp_Tinv` : stability under `f ↦ f ∘ T^{±1}`
  (the approximants are unchanged: `(f ∘ T) ∘ Tⁿ = f ∘ T^{n+1}`);
* `compactClass_of_measurable` : every bounded `D.σ`-measurable function is in 𝔄 (a net of
  constants on a grid, using `fibreNorm D (g - c) x = |g x - c|` for `D`-measurable `g`);
* `compactClass_sub`, `compactClass_abs`, `compactClass_clamp`: the lattice operations; for
  `Sigma.lean`,
  `1_{g>c}` is the `L²` limit of `x ↦ max 0 (min (k * (g x - c)) 1)`, which is
  `compactClass_clamp (compactClass_sub hg (compactClass_of_measurable measurable_const ..)` after
  `compactClass_smul`.

**Choice of statement.**  Every result is a closure property of the `Set (S.X → ℝ)`
`compactClass D` on actual functions (pointwise formulas such as `fun x => max (f x) (g x)`), with
no a.e. identification and no `L²`-class; `Sigma.lean` takes the `L²`-closure itself.  Membership of
a
function in `compactClass D` already includes measurability and boundedness, so each operation
re-proves those.

The common tool is the a.e. fibre estimate `fibreNorm_le_add`: if `|w| ≤ K₁|u| + K₂|v|` a.e. and
`u, v, w ∈ L²(m)`, then `‖w‖_x ≤ K₁‖u‖_x + K₂‖v‖_x` for a.e. `x`.
-/

@[expose] public section

namespace CantorSzemeredi.Proof

open MeasureTheory CSZPort CSZPort.MPS

variable {S : MPS} [StandardBorelSpace S.X]

/-! ### The fibre estimate -/

omit [StandardBorelSpace S.X] in
/-- On a probability space, `sqrt (∫ f²)` is the real `L²` norm. -/
theorem sqrt_integral_sq_eq {ν : Measure S.X} {f : S.X → ℝ} (hf : MemLp f 2 ν) :
    Real.sqrt (∫ y, f y ^ 2 ∂ν) = (eLpNorm f 2 ν).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  rw [Real.sqrt_eq_rpow]
  simp [sq_abs]

omit [StandardBorelSpace S.X] in
/-- The fibre estimate on a single measure. -/
theorem sqrt_integral_sq_le_add {ν : Measure S.X} {w u v : S.X → ℝ} (hw : MemLp w 2 ν)
    (hu : MemLp u 2 ν) (hv : MemLp v 2 ν) {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h : ∀ᵐ y ∂ν, |w y| ≤ K₁ * |u y| + K₂ * |v y|) :
    Real.sqrt (∫ y, w y ^ 2 ∂ν) ≤
      K₁ * Real.sqrt (∫ y, u y ^ 2 ∂ν) + K₂ * Real.sqrt (∫ y, v y ^ 2 ∂ν) := by
  rw [sqrt_integral_sq_eq hw, sqrt_integral_sq_eq hu, sqrt_integral_sq_eq hv]
  have hu1 : MemLp (fun y => K₁ * |u y|) 2 ν := by
    simpa [Real.norm_eq_abs] using (hu.norm.const_mul K₁)
  have hv1 : MemLp (fun y => K₂ * |v y|) 2 ν := by
    simpa [Real.norm_eq_abs] using (hv.norm.const_mul K₂)
  have e1 : eLpNorm w 2 ν ≤ eLpNorm (fun y => K₁ * |u y| + K₂ * |v y|) 2 ν :=
    eLpNorm_mono_ae_real hw.aestronglyMeasurable (h.mono fun y hy => by
      simpa [Real.norm_eq_abs] using hy)
  have e2 : eLpNorm (fun y => K₁ * |u y| + K₂ * |v y|) 2 ν ≤
      eLpNorm (fun y => K₁ * |u y|) 2 ν + eLpNorm (fun y => K₂ * |v y|) 2 ν :=
    eLpNorm_add_le (f := fun y => K₁ * |u y|) (g := fun y => K₂ * |v y|) (by norm_num)
  have e3 : ∀ (K : ℝ) (f : S.X → ℝ), 0 ≤ K → AEStronglyMeasurable f ν →
      eLpNorm (fun y => K * |f y|) 2 ν = ENNReal.ofReal K * eLpNorm f 2 ν := by
    intro K f hK hf
    have : (fun y => K * |f y|) = K • (fun y => ‖f y‖) := by
      funext y; simp [Real.norm_eq_abs]
    rw [this, eLpNorm_const_smul, eLpNorm_norm _ hf, Real.enorm_eq_ofReal hK]
  rw [e3 K₁ u hK₁ hu.aestronglyMeasurable, e3 K₂ v hK₂ hv.aestronglyMeasurable] at e2
  have hfin : ENNReal.ofReal K₁ * eLpNorm u 2 ν + ENNReal.ofReal K₂ * eLpNorm v 2 ν ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu.eLpNorm_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv.eLpNorm_ne_top⟩
  have := ENNReal.toReal_mono hfin (e1.trans e2)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu.eLpNorm_ne_top)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv.eLpNorm_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hK₁, ENNReal.toReal_ofReal hK₂] at this
  exact this

/-- A function in `L²(m)` is in `L²` of almost every fibre (no strong measurability needed). -/
theorem ae_memLp_condKernel' (D : Factor S) {g : S.X → ℝ} (hg : MemLp g 2 S.m) :
    ∀ᵐ x ∂S.m, MemLp g 2 (condKernel D x) := by
  have hmk : MemLp (hg.aestronglyMeasurable.mk g) 2 S.m := hg.ae_eq hg.aestronglyMeasurable.ae_eq_mk
  have h1 := ae_memLp_condKernel D hg.aestronglyMeasurable.stronglyMeasurable_mk hmk
  have h2 := ae_ae_condKernel_of_ae D hg.aestronglyMeasurable.ae_eq_mk
  filter_upwards [h1, h2] with x hx hx'
  exact hx.ae_eq (Filter.EventuallyEq.symm hx')

/-- **The fibre estimate.**  If `|w| ≤ K₁|u| + K₂|v|` almost everywhere, all in `L²(m)`, then
`‖w‖_x ≤ K₁‖u‖_x + K₂‖v‖_x` for almost every `x`. -/
theorem fibreNorm_le_add (D : Factor S) {w u v : S.X → ℝ} (hw : MemLp w 2 S.m)
    (hu : MemLp u 2 S.m) (hv : MemLp v 2 S.m) {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h : ∀ᵐ y ∂S.m, |w y| ≤ K₁ * |u y| + K₂ * |v y|) :
    ∀ᵐ x ∂S.m, fibreNorm D w x ≤ K₁ * fibreNorm D u x + K₂ * fibreNorm D v x := by
  filter_upwards [ae_memLp_condKernel' D hw, ae_memLp_condKernel' D hu,
    ae_memLp_condKernel' D hv, ae_ae_condKernel_of_ae D h] with x hw' hu' hv' h'
  exact sqrt_integral_sq_le_add hw' hu' hv' hK₁ hK₂ h'

/-! ### Orbit bookkeeping -/

omit [StandardBorelSpace S.X] in
theorem iter_succ_apply (n : ℤ) (x : S.X) : S.iter (n + 1) x = S.T (S.iter n x) := by
  cases n with
  | ofNat k =>
    have : (Int.ofNat k + 1 : ℤ) = ((k + 1 : ℕ) : ℤ) := by simp
    rw [this, S.iter_natCast, Function.iterate_succ_apply']
    rfl
  | negSucc k =>
    cases k with
    | zero => simp [MPS.iter]
    | succ k =>
      have : (Int.negSucc (k + 1) + 1 : ℤ) = Int.negSucc k := by
        simp only [Int.negSucc_eq]; push_cast; ring
      rw [this]
      simp only [MPS.iter]
      rw [Function.iterate_succ_apply' S.Tinv (k + 1)]
      simp

omit [StandardBorelSpace S.X] in
theorem iter_pred_apply (n : ℤ) (x : S.X) : S.iter (n - 1) x = S.Tinv (S.iter n x) := by
  cases n with
  | ofNat k =>
    cases k with
    | zero =>
      have : (Int.ofNat 0 - 1 : ℤ) = Int.negSucc 0 := rfl
      rw [this]
      simp [MPS.iter]
    | succ k =>
      have : (Int.ofNat (k + 1) - 1 : ℤ) = ((k : ℕ) : ℤ) := by simp
      rw [this, S.iter_natCast]
      simp only [Int.ofNat_eq_natCast, S.iter_natCast, Function.iterate_succ_apply']
      simp
  | negSucc k =>
    have : (Int.negSucc k - 1 : ℤ) = Int.negSucc (k + 1) := by
      simp only [Int.negSucc_eq]; push_cast; ring
    rw [this]
    simp only [MPS.iter]
    rw [Function.iterate_succ_apply' S.Tinv (k + 1)]

omit [StandardBorelSpace S.X] in
theorem comp_T_comp_iter (f : S.X → ℝ) (n : ℤ) :
    (f ∘ S.T) ∘ S.iter n = f ∘ S.iter (n + 1) := by
  funext x; simp [Function.comp, iter_succ_apply]

omit [StandardBorelSpace S.X] in
theorem comp_Tinv_comp_iter (f : S.X → ℝ) (n : ℤ) :
    (f ∘ S.Tinv) ∘ S.iter n = f ∘ S.iter (n - 1) := by
  funext x; simp [Function.comp, iter_pred_apply]

/-- **Stability under `f ↦ f ∘ T`.**  The approximants are unchanged. -/
theorem compactClass_comp_T {D : Factor S} {f : S.X → ℝ} (hf : f ∈ compactClass D) :
    f ∘ S.T ∈ compactClass D := by
  obtain ⟨hm, ⟨C, hC⟩, hcc⟩ := hf
  refine ⟨hm.comp S.measurable_T, ⟨C, fun x => hC _⟩, fun ε hε => ?_⟩
  obtain ⟨r, g, hg, h⟩ := hcc ε hε
  exact ⟨r, g, hg, fun n => by rw [comp_T_comp_iter]; exact h (n + 1)⟩

/-- **Stability under `f ↦ f ∘ T⁻¹`.** -/
theorem compactClass_comp_Tinv {D : Factor S} {f : S.X → ℝ} (hf : f ∈ compactClass D) :
    f ∘ S.Tinv ∈ compactClass D := by
  obtain ⟨hm, ⟨C, hC⟩, hcc⟩ := hf
  refine ⟨hm.comp S.measurable_Tinv, ⟨C, fun x => hC _⟩, fun ε hε => ?_⟩
  obtain ⟨r, g, hg, h⟩ := hcc ε hε
  exact ⟨r, g, hg, fun n => by rw [comp_Tinv_comp_iter]; exact h (n - 1)⟩

/-! ### Lipschitz images -/

omit [StandardBorelSpace S.X] in
theorem memLp_lipschitz_comp {φ : ℝ → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    {g : S.X → ℝ} (hg : MemLp g 2 S.m) : MemLp (φ ∘ g) 2 S.m := by
  have hb : MemLp (fun y => |φ 0| + (K : ℝ) * |g y|) 2 S.m := by
    refine (memLp_const _).add ?_
    simpa [Real.norm_eq_abs] using hg.norm.const_mul (K : ℝ)
  refine hb.mono' (hφ.continuous.comp_aestronglyMeasurable hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  have := hφ.dist_le_mul (g y) 0
  simp only [Real.dist_eq, sub_zero] at this
  simp only [Function.comp, Real.norm_eq_abs]
  calc |φ (g y)| = |φ 0 + (φ (g y) - φ 0)| := by ring_nf
    _ ≤ |φ 0| + |φ (g y) - φ 0| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- **Lipschitz images.**  If `f ∈ 𝔄` and `φ : ℝ → ℝ` is Lipschitz, then `φ ∘ f ∈ 𝔄`. -/
theorem compactClass_lipschitz {D : Factor S} {φ : ℝ → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) {f : S.X → ℝ} (hf : f ∈ compactClass D) :
    φ ∘ f ∈ compactClass D := by
  obtain ⟨hm, ⟨C, hC⟩, hcc⟩ := hf
  refine ⟨hφ.continuous.measurable.comp hm, ⟨|φ 0| + K * C, fun x => ?_⟩, fun ε hε => ?_⟩
  · have := hφ.dist_le_mul (f x) 0
    simp only [Real.dist_eq, sub_zero] at this
    have h2 : (K : ℝ) * |f x| ≤ K * C := mul_le_mul_of_nonneg_left (hC x) K.2
    simp only [Function.comp]
    calc |φ (f x)| = |φ 0 + (φ (f x) - φ 0)| := by ring_nf
      _ ≤ |φ 0| + |φ (f x) - φ 0| := abs_add_le _ _
      _ ≤ _ := by linarith
  · have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    obtain ⟨r, g, hg, h⟩ := hcc (ε / ((K : ℝ) + 1)) (by positivity)
    refine ⟨r, fun q => φ ∘ g q, fun q => memLp_lipschitz_comp hφ (hg q), fun n => ?_⟩
    have hfn : MemLp (f ∘ S.iter n) 2 S.m := memLp_two_of_bounded (hm.comp (S.measurable_iter n))
      (C := C) (fun x => hC _)
    have hφfn : MemLp ((φ ∘ f) ∘ S.iter n) 2 S.m :=
      memLp_lipschitz_comp hφ hfn
    have hall : ∀ᵐ x ∂S.m, ∀ q : Fin r, fibreNorm D ((φ ∘ f) ∘ S.iter n - φ ∘ g q) x ≤
        (K : ℝ) * fibreNorm D (f ∘ S.iter n - g q) x
          + 0 * fibreNorm D (f ∘ S.iter n - g q) x :=
      ae_all_iff.2 fun q => fibreNorm_le_add D (hφfn.sub (memLp_lipschitz_comp hφ (hg q)))
        (hfn.sub (hg q)) (hfn.sub (hg q)) K.2 le_rfl (Filter.Eventually.of_forall fun y => by
          have := hφ.dist_le_mul (f (S.iter n y)) (g q y)
          simp only [Real.dist_eq] at this
          simpa using this)
    filter_upwards [h n, hall] with x ⟨q, hq⟩ hall'
    refine ⟨q, ?_⟩
    have h1 := hall' q
    have h2 : (K : ℝ) * fibreNorm D (f ∘ S.iter n - g q) x ≤
        K * (ε / ((K : ℝ) + 1)) := mul_le_mul_of_nonneg_left hq.le K.2
    have h3 : (K : ℝ) * (ε / ((K : ℝ) + 1)) < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ hK]; nlinarith
    linarith

/-- Product-index bookkeeping: `Fin r₁ × Fin r₂` re-indexed by `Fin (r₁ * r₂)`. -/
theorem condCompactZ_of_pairs {D : Factor S} {F : S.X → ℝ} {ε : ℝ} {r₁ r₂ : ℕ}
    (G : Fin r₁ → Fin r₂ → S.X → ℝ) (hG : ∀ a b, MemLp (G a b) 2 S.m)
    (h : ∀ n : ℤ, ∀ᵐ x ∂S.m, ∃ a b, fibreNorm D (F ∘ S.iter n - G a b) x < ε) :
    ∃ (r : ℕ) (g : Fin r → S.X → ℝ), (∀ q, MemLp (g q) 2 S.m) ∧
      ∀ n : ℤ, ∀ᵐ x ∂S.m, ∃ q : Fin r, fibreNorm D (F ∘ S.iter n - g q) x < ε := by
  refine ⟨r₁ * r₂, fun k => G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2,
    fun k => hG _ _, fun n => ?_⟩
  filter_upwards [h n] with x ⟨a, b, hab⟩
  exact ⟨finProdFinEquiv (a, b), by simpa using hab⟩

/-- **Sums.** -/
theorem compactClass_add {D : Factor S} {f g : S.X → ℝ} (hf : f ∈ compactClass D)
    (hg : g ∈ compactClass D) : f + g ∈ compactClass D := by
  obtain ⟨hfm, ⟨C₁, hC₁⟩, hf'⟩ := hf
  obtain ⟨hgm, ⟨C₂, hC₂⟩, hg'⟩ := hg
  refine ⟨hfm.add hgm, ⟨C₁ + C₂, fun x => (abs_add_le _ _).trans (add_le_add (hC₁ x) (hC₂ x))⟩,
    fun ε hε => ?_⟩
  obtain ⟨r₁, a, ha, h₁⟩ := hf' (ε / 2) (by positivity)
  obtain ⟨r₂, b, hb, h₂⟩ := hg' (ε / 2) (by positivity)
  refine condCompactZ_of_pairs (fun i j => a i + b j) (fun i j => (ha i).add (hb j)) fun n => ?_
  have hfn : MemLp (f ∘ S.iter n) 2 S.m := memLp_two_of_bounded (hfm.comp (S.measurable_iter n))
    (C := C₁) (fun x => hC₁ _)
  have hgn : MemLp (g ∘ S.iter n) 2 S.m := memLp_two_of_bounded (hgm.comp (S.measurable_iter n))
    (C := C₂) (fun x => hC₂ _)
  have hall : ∀ᵐ x ∂S.m, ∀ p : Fin r₁ × Fin r₂,
      fibreNorm D ((f + g) ∘ S.iter n - (a p.1 + b p.2)) x ≤
        1 * fibreNorm D (f ∘ S.iter n - a p.1) x + 1 * fibreNorm D (g ∘ S.iter n - b p.2) x :=
    ae_all_iff.2 fun p => fibreNorm_le_add D
      (((hfn.add hgn)).sub ((ha p.1).add (hb p.2))) (hfn.sub (ha p.1)) (hgn.sub (hb p.2))
      zero_le_one zero_le_one (Filter.Eventually.of_forall fun y => by
        simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, one_mul]
        calc _ = |(f (S.iter n y) - a p.1 y) + (g (S.iter n y) - b p.2 y)| := by ring_nf
          _ ≤ _ := abs_add_le _ _)
  filter_upwards [h₁ n, h₂ n, hall] with x ⟨i, hi⟩ ⟨j, hj⟩ hh
  exact ⟨i, j, by have := hh (i, j); simp only at this; linarith⟩

omit [StandardBorelSpace S.X] in
theorem lipschitzWith_const_mul (c : ℝ) : LipschitzWith ‖c‖₊ (fun t : ℝ => c * t) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simp [dist_eq_norm, ← mul_sub, norm_mul]

omit [StandardBorelSpace S.X] in
theorem lipschitzWith_abs : LipschitzWith 1 (fun t : ℝ => |t|) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y

omit [StandardBorelSpace S.X] in
theorem lipschitzWith_clamp (lo hi : ℝ) : LipschitzWith 1 (fun t : ℝ => max lo (min t hi)) :=
  (LipschitzWith.id.min_const hi).const_max lo

/-- **Scalar multiples.** -/
theorem compactClass_smul {D : Factor S} {f : S.X → ℝ} (hf : f ∈ compactClass D) (c : ℝ) :
    (fun x => c * f x) ∈ compactClass D :=
  compactClass_lipschitz (lipschitzWith_const_mul c) hf

/-- **Absolute value.** -/
theorem compactClass_abs {D : Factor S} {f : S.X → ℝ} (hf : f ∈ compactClass D) :
    (fun x => |f x|) ∈ compactClass D :=
  compactClass_lipschitz lipschitzWith_abs hf

/-- **Clamp.**  `x ↦ max lo (min (f x) hi)` is in 𝔄 for every `lo hi`; with
`f ↦ k * (f - c)` and `lo = 0`, `hi = 1` this is the approximation of `1_{f > c}` used for
`compactFactor`. -/
theorem compactClass_clamp {D : Factor S} {f : S.X → ℝ} (hf : f ∈ compactClass D)
    (lo hi : ℝ) : (fun x => max lo (min (f x) hi)) ∈ compactClass D :=
  compactClass_lipschitz (lipschitzWith_clamp lo hi) hf

/-- **Differences.** -/
theorem compactClass_sub {D : Factor S} {f g : S.X → ℝ} (hf : f ∈ compactClass D)
    (hg : g ∈ compactClass D) : (fun x => f x - g x) ∈ compactClass D := by
  have := compactClass_add hf (compactClass_smul hg (-1))
  convert this using 1
  funext x; simp [sub_eq_add_neg]

/-- **Maximum.** -/
theorem compactClass_max {D : Factor S} {f g : S.X → ℝ} (hf : f ∈ compactClass D)
    (hg : g ∈ compactClass D) : (fun x => max (f x) (g x)) ∈ compactClass D := by
  have h := compactClass_smul (compactClass_add (compactClass_add hf hg)
    (compactClass_abs (compactClass_sub hf hg))) (1 / 2)
  convert h using 1
  funext x
  simp only [Pi.add_apply]
  rcases le_total (f x) (g x) with hle | hle
  · rw [max_eq_right hle, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left hle, abs_of_nonneg (by linarith)]; ring

/-- **Minimum.** -/
theorem compactClass_min {D : Factor S} {f g : S.X → ℝ} (hf : f ∈ compactClass D)
    (hg : g ∈ compactClass D) : (fun x => min (f x) (g x)) ∈ compactClass D := by
  have h := compactClass_smul (compactClass_sub (compactClass_add hf hg)
    (compactClass_abs (compactClass_sub hf hg))) (1 / 2)
  convert h using 1
  funext x
  simp only [Pi.add_apply]
  rcases le_total (f x) (g x) with hle | hle
  · rw [min_eq_left hle, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right hle, abs_of_nonneg (by linarith)]; ring

omit [StandardBorelSpace S.X] in
theorem abs_clamp_le {C : ℝ} (hC : 0 ≤ C) (t : ℝ) : |max (-C) (min t C)| ≤ C :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

omit [StandardBorelSpace S.X] in
theorem clamp_self {C : ℝ} {t : ℝ} (ht : |t| ≤ C) : max (-C) (min t C) = t := by
  rw [abs_le] at ht
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- **Bounded products.** -/
theorem compactClass_mul {D : Factor S} {f g : S.X → ℝ} (hf : f ∈ compactClass D)
    (hg : g ∈ compactClass D) : (fun x => f x * g x) ∈ compactClass D := by
  obtain ⟨hfm, ⟨C₁', hC₁'⟩, hf'⟩ := hf
  obtain ⟨hgm, ⟨C₂', hC₂'⟩, hg'⟩ := hg
  set C₁ : ℝ := max C₁' 0 with hC₁def
  set C₂ : ℝ := max C₂' 0 with hC₂def
  have hC₁ : ∀ x, |f x| ≤ C₁ := fun x => (hC₁' x).trans (le_max_left _ _)
  have hC₂ : ∀ x, |g x| ≤ C₂ := fun x => (hC₂' x).trans (le_max_left _ _)
  have h₁0 : 0 ≤ C₁ := le_max_right _ _
  have h₂0 : 0 ≤ C₂ := le_max_right _ _
  refine ⟨hfm.mul hgm, ⟨C₁ * C₂, fun x => ?_⟩, fun ε hε => ?_⟩
  · rw [abs_mul]; exact mul_le_mul (hC₁ x) (hC₂ x) (abs_nonneg _) h₁0
  have hpos : 0 < C₁ + C₂ + 1 := by linarith
  set δ : ℝ := ε / (C₁ + C₂ + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hδε : δ * (C₁ + C₂ + 1) = ε := div_mul_cancel₀ _ hpos.ne'
  obtain ⟨r₁, a, ha, h₁⟩ := hf' δ hδ
  obtain ⟨r₂, b, hb, h₂⟩ := hg' δ hδ
  have hA : ∀ i, MemLp (fun y => max (-C₁) (min (a i y) C₁)) 2 S.m := fun i =>
    memLp_lipschitz_comp (lipschitzWith_clamp (-C₁) C₁) (ha i)
  have hB : ∀ j, MemLp (fun y => max (-C₂) (min (b j y) C₂)) 2 S.m := fun j =>
    memLp_lipschitz_comp (lipschitzWith_clamp (-C₂) C₂) (hb j)
  have hAB : ∀ i j, MemLp (fun y => max (-C₁) (min (a i y) C₁) * max (-C₂) (min (b j y) C₂))
      2 S.m := fun i j =>
    (hA i).of_le_mul (c := C₂) ((hA i).aestronglyMeasurable.mul (hB j).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by
        simp only [Real.norm_eq_abs, abs_mul]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (abs_clamp_le h₂0 _) (abs_nonneg _))
  refine condCompactZ_of_pairs (fun i j y => max (-C₁) (min (a i y) C₁) *
    max (-C₂) (min (b j y) C₂)) hAB fun n => ?_
  have hfn : MemLp (f ∘ S.iter n) 2 S.m := memLp_two_of_bounded (hfm.comp (S.measurable_iter n))
    (C := C₁) (fun x => hC₁ _)
  have hgn : MemLp (g ∘ S.iter n) 2 S.m := memLp_two_of_bounded (hgm.comp (S.measurable_iter n))
    (C := C₂) (fun x => hC₂ _)
  have hfg : MemLp ((fun x => f x * g x) ∘ S.iter n) 2 S.m :=
    memLp_two_of_bounded ((hfm.mul hgm).comp (S.measurable_iter n)) (C := C₁ * C₂)
      (fun x => by
        simp only [Function.comp, abs_mul]
        exact mul_le_mul (hC₁ _) (hC₂ _) (abs_nonneg _) h₁0)
  have hall : ∀ᵐ x ∂S.m, ∀ p : Fin r₁ × Fin r₂,
      fibreNorm D ((fun x => f x * g x) ∘ S.iter n - (fun y => max (-C₁) (min (a p.1 y) C₁) *
          max (-C₂) (min (b p.2 y) C₂))) x ≤
        C₂ * fibreNorm D (f ∘ S.iter n - a p.1) x + C₁ * fibreNorm D (g ∘ S.iter n - b p.2) x :=
    ae_all_iff.2 fun p => fibreNorm_le_add D (hfg.sub (hAB p.1 p.2)) (hfn.sub (ha p.1))
      (hgn.sub (hb p.2)) h₂0 h₁0 (Filter.Eventually.of_forall fun y => by
        simp only [Pi.sub_apply, Function.comp_apply]
        set F := f (S.iter n y)
        set G := g (S.iter n y)
        have hF : |F| ≤ C₁ := hC₁ _
        have hG : |G| ≤ C₂ := hC₂ _
        have hFa : |F - max (-C₁) (min (a p.1 y) C₁)| ≤ |F - a p.1 y| := by
          have := (lipschitzWith_clamp (-C₁) C₁).dist_le_mul F (a p.1 y)
          simpa [Real.dist_eq, clamp_self hF] using this
        have hGb : |G - max (-C₂) (min (b p.2 y) C₂)| ≤ |G - b p.2 y| := by
          have := (lipschitzWith_clamp (-C₂) C₂).dist_le_mul G (b p.2 y)
          simpa [Real.dist_eq, clamp_self hG] using this
        set A := max (-C₁) (min (a p.1 y) C₁)
        set B := max (-C₂) (min (b p.2 y) C₂)
        have e : F * G - A * B = (F - A) * G + A * (G - B) := by ring
        rw [e]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        have t1 : |F - A| * |G| ≤ |F - a p.1 y| * C₂ :=
          mul_le_mul hFa hG (abs_nonneg _) (abs_nonneg _)
        have t2 : |A| * |G - B| ≤ C₁ * |G - b p.2 y| :=
          mul_le_mul (abs_clamp_le h₁0 _) hGb (abs_nonneg _) h₁0
        linarith)
  filter_upwards [h₁ n, h₂ n, hall] with x ⟨i, hi⟩ ⟨j, hj⟩ hh
  refine ⟨i, j, ?_⟩
  have := hh (i, j)
  simp only at this
  have t1 : C₂ * fibreNorm D (f ∘ S.iter n - a i) x ≤ C₂ * δ :=
    mul_le_mul_of_nonneg_left hi.le h₂0
  have t2 : C₁ * fibreNorm D (g ∘ S.iter n - b j) x ≤ C₁ * δ :=
    mul_le_mul_of_nonneg_left hj.le h₁0
  nlinarith

/-! ### `D`-measurable functions -/

omit [StandardBorelSpace S.X] in
theorem measurable_T_D (D : Factor S) : @Measurable S.X S.X D.σ D.σ S.T :=
  fun _ hs => D.measurableSet_preimage hs

omit [StandardBorelSpace S.X] in
theorem measurable_Tinv_D (D : Factor S) : @Measurable S.X S.X D.σ D.σ S.Tinv := by
  intro s hs
  refine (D.invariant _).1 ?_
  have : S.T ⁻¹' (S.Tinv ⁻¹' s) = s := by ext x; simp
  rw [this]; exact hs

omit [StandardBorelSpace S.X] in
theorem measurable_iter_D (D : Factor S) (n : ℤ) : @Measurable S.X S.X D.σ D.σ (S.iter n) := by
  induction n using Int.induction_on with
  | zero => exact measurable_id
  | succ i ih =>
    have : S.iter ((i : ℤ) + 1) = S.T ∘ S.iter i := funext fun x => iter_succ_apply _ _
    rw [this]; exact (measurable_T_D D).comp ih
  | pred i ih =>
    have : S.iter (-(i : ℤ) - 1) = S.Tinv ∘ S.iter (-(i : ℤ)) :=
      funext fun x => iter_pred_apply _ _
    rw [this]; exact (measurable_Tinv_D D).comp ih

/-- For a bounded `D`-measurable `h` and a constant `c`, `‖h - c‖_x = |h x - c|` a.e. -/
theorem fibreNorm_sub_const_ae (D : Factor S) {h : S.X → ℝ} (hh : Measurable[D.σ] h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) (c : ℝ) :
    ∀ᵐ x ∂S.m, fibreNorm D (h - fun _ => c) x = |h x - c| := by
  have hha : Measurable h := hh.mono D.le le_rfl
  have hmem : MemLp (h - fun _ => c) 2 S.m :=
    (memLp_two_of_bounded hha hC).sub (memLp_const c)
  have hint : Integrable (fun y => (h y - c) ^ 2) S.m := hmem.integrable_sq
  have hsm : StronglyMeasurable[D.σ] (fun y => (h y - c) ^ 2) :=
    ((hh.sub_const c).pow_const 2).stronglyMeasurable
  have hce := congrFun (condExp_of_stronglyMeasurable D.le hsm hint) 
  filter_upwards [condExp_eq_integral_condKernel D hint] with x hx
  change Real.sqrt (∫ y, (h y - c) ^ 2 ∂(condKernel D x)) = _
  rw [← hx, hce x, Real.sqrt_sq_eq_abs]

/-- **`L^∞(D) ⊆ 𝔄`.**  Every bounded `D`-measurable function lies in 𝔄. -/
theorem compactClass_of_measurable {D : Factor S} {g : S.X → ℝ} (hg : Measurable[D.σ] g)
    (hb : ∃ C : ℝ, ∀ x, |g x| ≤ C) : g ∈ compactClass D := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨hg.mono D.le le_rfl, ⟨C, hC⟩, fun ε hε => ?_⟩
  set N : ℕ := ⌈C / ε⌉₊ with hN
  refine ⟨2 * N + 1, fun q _ => (((q : ℕ) : ℝ) - N) * ε, fun q => memLp_const _, fun n => ?_⟩
  have hgn : Measurable[D.σ] (g ∘ S.iter n) := hg.comp (measurable_iter_D D n)
  have hall : ∀ᵐ x ∂S.m, ∀ q : Fin (2 * N + 1),
      fibreNorm D (g ∘ S.iter n - fun _ => (((q : ℕ) : ℝ) - N) * ε) x =
        |g (S.iter n x) - (((q : ℕ) : ℝ) - N) * ε| :=
    ae_all_iff.2 fun q => fibreNorm_sub_const_ae D hgn (C := C) (fun x => hC _) _
  filter_upwards [hall] with x hx
  set t := g (S.iter n x) with ht
  have htC : |t| ≤ C := hC _
  have hCN : C / ε ≤ N := Nat.le_ceil _
  have hlow : -(N : ℝ) ≤ t / ε := by
    rw [le_div_iff₀ hε]
    have := (abs_le.1 htC).1
    have h2 : C ≤ N * ε := by rwa [div_le_iff₀ hε] at hCN
    linarith
  have hhigh : t / ε ≤ N := by
    rw [div_le_iff₀ hε]
    have := (abs_le.1 htC).2
    have h2 : C ≤ N * ε := by rwa [div_le_iff₀ hε] at hCN
    linarith
  have hfl1 : -(N : ℤ) ≤ ⌊t / ε⌋ := Int.le_floor.2 (by simpa using hlow)
  have hfl2 : ⌊t / ε⌋ ≤ (N : ℤ) := Int.floor_le_iff.2 (by
    have : t / ε < (N : ℝ) + 1 := by linarith
    simpa using this)
  have hj : (⌊t / ε⌋ + N).toNat < 2 * N + 1 := by omega
  refine ⟨⟨(⌊t / ε⌋ + N).toNat, hj⟩, ?_⟩
  rw [hx]
  have hcast : (((⌊t / ε⌋ + N).toNat : ℕ) : ℝ) = (⌊t / ε⌋ : ℝ) + N := by
    have : (((⌊t / ε⌋ + N).toNat : ℕ) : ℤ) = ⌊t / ε⌋ + N := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  simp only [hcast, add_sub_cancel_right]
  have h1 : (⌊t / ε⌋ : ℝ) ≤ t / ε := Int.floor_le _
  have h2 : t / ε < (⌊t / ε⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hε] at h1
  rw [div_lt_iff₀ hε] at h2
  rw [abs_lt]
  constructor <;> nlinarith

end CantorSzemeredi.Proof

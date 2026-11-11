module

public import CantorSzemeredi.Port.Dynamics.Atomless
public import CantorSzemeredi.Port.Dynamics.Koopman
public import CantorSzemeredi.Port.Dynamics.Joining
public import CantorSzemeredi.Port.Dynamics.Spectral
public import CantorSzemeredi.Port.Dynamics.SpectralExists

/-!
# Eigenvector of the atom, orthogonal to the tensors over `D`

* `exists_eigenvector_mem_closure_span_of_atom`: a spectral atom of `v` for a unitary `U`
  gives an eigenvector `w ≠ 0` with eigenvalue `e(θ)` lying in the closed span of the orbit
  `{Uⁿ v : n : ℤ}` (strengthening of the ported `exists_eigenvector_of_atom`).
* `IsTensorD D g` : `g ∈ L²(λ)` is a.e. a product `u(x) v(y)` of bounded measurable real
  functions, one of them `D`-measurable.
* `inner_tensorSq_eq_zero` : `G = f ⊗ f` is orthogonal to every such `g` when `E(f|D) = 0`.
* `isTensorD_koopman_zpow` : the class is invariant under the powers of the Koopman operator
  of the product system.
* `exists_eigenvector_orthogonal_tensors` (the form consumed by `exists_kernel_data`): from an atom
  of the
  spectral measure of `G = f ⊗ f` we get an eigenvector `w ≠ 0` of the Koopman operator of the
  product system, orthogonal to all `IsTensorD D` elements.
-/

@[expose] public section

namespace CantorSzemeredi.Proof

open MeasureTheory CSZPort CSZPort.MPS

/-! ### Eigenvector in the span of the orbit -/

section SpectralAtom

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- If the spectral measure of `U` at `v` has an atom at `θ`, there is an eigenvector
`w ≠ 0` with eigenvalue `e(θ)` in the closed span of the orbit `{Uⁿ v : n : ℤ}`. -/
theorem exists_eigenvector_mem_closure_span_of_atom [CompleteSpace H] {U : H ≃ₗᵢ[ℂ] H} {v : H}
    {σ : Measure Torus} (h : HasSpectralMeasure U v σ) {θ : Torus} (hθ : σ {θ} ≠ 0) :
    ∃ w : H, w ≠ 0 ∧ U w = fourier 1 θ • w ∧
      w ∈ (Submodule.span ℂ (Set.range fun n : ℤ => (U ^ n) v)).topologicalClosure := by
  classical
  have hfin := h.isFinite
  set c : ℂ := (starRingEnd ℂ) (fourier 1 θ) with hc
  have hcnorm : ‖c‖ = 1 := by
    rw [hc, RCLike.norm_conj, fourier_apply]
    exact Circle.norm_coe _
  set W : H →L[ℂ] H := c • (U.toLinearIsometry.toContinuousLinearMap) with hW
  have hWnorm : ‖W‖ ≤ 1 := by
    rw [hW, norm_smul, hcnorm, one_mul]
    exact LinearIsometry.norm_toContinuousLinearMap_le U.toLinearIsometry
  have hiter : ∀ (n : ℕ) (x : H), W^[n] x = (c ^ n) • (U ^ (n : ℤ)) x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, hW]
      simp only [smul_apply, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry, map_smul]
      have hUU : U ((U ^ (n : ℤ)) x) = (U ^ ((n + 1 : ℕ) : ℤ)) x := by
        rw [show (((n + 1 : ℕ)) : ℤ) = 1 + (n : ℤ) by push_cast; ring,
          zpow_add U 1 (n : ℤ), zpow_one]
        rfl
      rw [hUU, smul_smul, pow_succ, mul_comm (c ^ n) c]
  have hbirk : ∀ N : ℕ, birkhoffAverage ℂ W _root_.id N v
      = ∑ n ∈ Finset.range N, ((N : ℂ)⁻¹ * c ^ n) • (U ^ (n : ℤ)) v := by
    intro N
    rw [birkhoffAverage, birkhoffSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show _root_.id (W^[n] v) = W^[n] v from rfl, hiter n v, smul_smul]
  set Psub := (W.eqLocus (1 : H →L[ℂ] H)).orthogonalProjectionOnto v with hPsub
  set w : H := (Psub : H) with hw
  have hme := W.tendsto_birkhoffAverage_orthogonalProjection hWnorm v
  have hcpow : ∀ n : ℕ, c ^ n = (starRingEnd ℂ) (fourier (n : ℤ) θ) := by
    intro n
    rw [hc, ← map_pow]
    congr 1
    rw [fourier_eq_zpow (n : ℤ) θ, zpow_natCast]
  have hnormlim := h.tendsto_norm_birkhoff_sq θ
  have hnormlim' : Filter.Tendsto (fun N : ℕ => ‖birkhoffAverage ℂ W _root_.id N v‖ ^ 2)
      Filter.atTop (nhds ((σ {θ}).toReal)) := by
    refine hnormlim.congr fun N => ?_
    rw [hbirk N]
    congr 2
    exact Finset.sum_congr rfl fun n _ => by rw [hcpow n]
  have hlim : Filter.Tendsto (fun N : ℕ => ‖birkhoffAverage ℂ W _root_.id N v‖ ^ 2)
      Filter.atTop (nhds (‖w‖ ^ 2)) :=
    ((continuous_pow 2).continuousAt.tendsto.comp ((continuous_norm.tendsto _).comp hme))
  have hwnorm : ‖w‖ ^ 2 = (σ {θ}).toReal := tendsto_nhds_unique hlim hnormlim'
  have hwne : w ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hwnorm
    refine hθ ?_
    have hz : (σ {θ}).toReal = 0 := by simpa using hwnorm.symm
    exact (ENNReal.toReal_eq_zero_iff _).1 hz |>.resolve_right (measure_ne_top _ _)
  refine ⟨w, hwne, ?_, ?_⟩
  · have hfix : c • U w = w := by
      have hmem : W w = w := Psub.2
      rw [hW] at hmem
      simpa using hmem
    have hcinv : (fourier 1 θ) * c = 1 := by
      rw [hc, mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
        show ‖fourier (1 : ℤ) θ‖ = 1 by rw [fourier_apply]; exact Circle.norm_coe _]
      norm_num
    calc U w = (fourier 1 θ * c) • U w := by rw [hcinv, one_smul]
      _ = fourier 1 θ • (c • U w) := by rw [smul_smul]
      _ = fourier 1 θ • w := by rw [hfix]
  · refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hme
      (Filter.Eventually.of_forall fun N => ?_)
    refine Submodule.le_topologicalClosure _ ?_
    rw [hbirk N]
    exact Submodule.sum_mem _ fun n _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(n : ℤ), rfl⟩)

end SpectralAtom

/-! ### Eigenvector orthogonal to the tensors -/

section TensorOrthogonal

variable {S : MPS}

/-- `S.iter n` is `D`-`D`-measurable. -/
theorem measurable_iter_factor (D : Factor S) (n : ℤ) :
    @Measurable S.X S.X D.σ D.σ (S.iter n) := by
  have hT : @Measurable S.X S.X D.σ D.σ S.T := fun s hs => D.measurableSet_preimage hs
  have hTinv : @Measurable S.X S.X D.σ D.σ S.Tinv := by
    intro s hs
    have : S.Tinv ⁻¹' s = S.T '' s := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx; exact ⟨_, hx, S.T_Tinv x⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [this]
    exact D.measurableSet_image hs
  cases n with
  | ofNat n => exact hT.iterate n
  | negSucc n => exact hTinv.iterate (n + 1)

variable [StandardBorelSpace S.X]

/-- The inverse of the product transformation acts coordinatewise. -/
theorem prodSystem_Tinv (D : Factor S) (p : S.X × S.X) :
    (prodSystem D).Tinv p = (S.Tinv p.1, S.Tinv p.2) := by
  have h : (prodSystem D).T (S.Tinv p.1, S.Tinv p.2) = p := by
    show prodMap S (S.Tinv p.1, S.Tinv p.2) = p
    simp [prodMap]
  conv_lhs => rw [← h]
  exact (prodSystem D).Tinv_T _

/-- The integer iterates of the product transformation act coordinatewise. -/
theorem prodSystem_iter_int (D : Factor S) (n : ℤ) (p : S.X × S.X) :
    (prodSystem D).iter n p = (S.iter n p.1, S.iter n p.2) := by
  cases n with
  | ofNat n => exact prodSystem_iter D n p
  | negSucc n =>
    show (prodSystem D).Tinv^[n + 1] p = (S.Tinv^[n + 1] p.1, S.Tinv^[n + 1] p.2)
    generalize n + 1 = k
    induction k generalizing p with
    | zero => rfl
    | succ k ih =>
      exact (Function.iterate_succ_apply' _ _ _).trans
        ((congrArg (prodSystem D).Tinv (ih p)).trans ((prodSystem_Tinv D _).trans
          (by simp [Function.iterate_succ_apply'])))

/-- **The class of tensors over `D`.**  `g ∈ L²(λ)` is a.e. a product `u(x) v(y)` of bounded
measurable real functions, at least one of which is `D`-measurable. -/
def IsTensorD (D : Factor S) (g : Lp ℂ 2 (prodSystem D).m) : Prop :=
  ∃ u v : S.X → ℝ, Measurable u ∧ Measurable v ∧ (∃ C, ∀ x, |u x| ≤ C) ∧
    (∃ C, ∀ x, |v x| ≤ C) ∧ (Measurable[D.σ] u ∨ Measurable[D.σ] v) ∧
    g =ᵐ[(prodSystem D).m] fun p : S.X × S.X => ((u p.1 * v p.2 : ℝ) : ℂ)

/-- The class `IsTensorD` is invariant under the powers of the Koopman operator. -/
theorem isTensorD_koopman_zpow (D : Factor S) {g : Lp ℂ 2 (prodSystem D).m}
    (hg : IsTensorD D g) (n : ℤ) : IsTensorD D (((prodSystem D).koopman ^ n) g) := by
  obtain ⟨u, v, hu, hv, ⟨Cu, hCu⟩, ⟨Cv, hCv⟩, hD, hgae⟩ := hg
  refine ⟨u ∘ S.iter n, v ∘ S.iter n, hu.comp (S.measurable_iter n), hv.comp (S.measurable_iter n),
    ⟨Cu, fun x => hCu _⟩, ⟨Cv, fun x => hCv _⟩, ?_, ?_⟩
  · rcases hD with hD | hD
    · exact Or.inl (hD.comp (measurable_iter_factor D n))
    · exact Or.inr (hD.comp (measurable_iter_factor D n))
  · have h1 := (prodSystem D).coeFn_koopman_zpow n g
    have h2 := ((prodSystem D).measurePreserving_iter n).quasiMeasurePreserving.ae_eq_comp hgae
    filter_upwards [h1, h2] with p hp hp'
    exact (hp.trans hp').trans
      (congrArg (fun q : S.X × S.X => (((u q.1 * v q.2 : ℝ)) : ℂ)) (prodSystem_iter_int D n p))

/-- `G = f ⊗ f` is orthogonal to every tensor over `D` when `E(f|D) = 0`. -/
theorem inner_tensorSq_eq_zero (D : Factor S) {f : S.X → ℝ} {C : ℝ}
    (hm : Measurable f) (hb : ∀ x, |f x| ≤ C) (hcond : S.m[f|D.σ] =ᵐ[S.m] 0)
    {g : Lp ℂ 2 (prodSystem D).m} (hg : IsTensorD D g) :
    inner ℂ g (toLpC (prodSystem D) (measurable_tensorSq hm) (abs_tensorSq_le hb)) = 0 := by
  obtain ⟨u, v, hu, hv, ⟨Cu, hCu⟩, ⟨Cv, hCv⟩, hD, hgae⟩ := hg
  rw [L2.inner_def]
  have hpt : ∀ᵐ p ∂(prodSystem D).m,
      (inner ℂ (g p) (toLpC (prodSystem D) (measurable_tensorSq hm) (abs_tensorSq_le hb) p) : ℂ)
        = (((u p.1 * f p.1) * (v p.2 * f p.2) : ℝ) : ℂ) := by
    filter_upwards [hgae, coeFn_toLpC (S := prodSystem D) (measurable_tensorSq hm)
      (abs_tensorSq_le hb)] with p h1 h2
    rw [h1, h2]
    simp only [RCLike.inner_apply, tensorSq, Complex.conj_ofReal]
    push_cast
    ring
  rw [integral_congr_ae hpt, integral_complex_ofReal]
  have hbd : ∀ {w : S.X → ℝ} {c : ℝ}, (∀ x, |w x| ≤ c) → ∀ x, |w x * f x| ≤ c * C := by
    intro w c hw x
    have hc0 : (0 : ℝ) ≤ c := (abs_nonneg _).trans (hw x)
    rw [abs_mul]
    exact mul_le_mul (hw x) (hb x) (abs_nonneg _) hc0
  have key := integral_joining D (a := fun x => u x * f x) (a' := fun x => v x * f x)
    (hu.mul hm) (hv.mul hm) (hbd hCu) (hbd hCv)
  have hint : Integrable f S.m :=
    (memLp_top_of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hb x)).integrable le_top
  have hz : ∀ {w : S.X → ℝ} {c : ℝ}, Measurable[D.σ] w → (∀ x, |w x| ≤ c) →
      S.m[(fun x => w x * f x)|D.σ] =ᵐ[S.m] 0 := by
    intro w c hw hwb
    have := condExp_stronglyMeasurable_mul_of_bound D.le (μ := S.m) (f := w) (g := f)
      hw.stronglyMeasurable hint c (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hwb x)
    filter_upwards [this, hcond] with x hx hx'
    rw [show (fun x => w x * f x) = w * f from rfl, hx]
    simp [hx']
  have hzero : ∫ x, (S.m[(fun x => u x * f x)|D.σ]) x * (S.m[(fun x => v x * f x)|D.σ]) x ∂S.m
      = 0 := by
    rcases hD with hD | hD
    · have := hz hD hCu
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      · filter_upwards [this] with x hx
        simp [hx]
    · have := hz hD hCv
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      · filter_upwards [this] with x hx
        simp [hx]
  rw [hzero] at key
  have key' : ∫ p : S.X × S.X, ((u p.1 * f p.1) * (v p.2 * f p.2)) ∂(prodSystem D).m = 0 := key
  exact (congrArg (fun r : ℝ => (r : ℂ)) key').trans (by simp)

/-- **The form consumed by `exists_kernel_data`.**  Let `f` be bounded measurable with `E(f|D) = 0`,
and
suppose the spectral measure of `G = f ⊗ f` for the Koopman operator of the product system has
an atom at `θ`.  Then the Koopman operator `U` of the product system has an eigenvector
`w ≠ 0` with eigenvalue `e(θ)` which is orthogonal to every tensor `u(x) v(y)` over `D`
(`IsTensorD`). -/
theorem exists_eigenvector_orthogonal_tensors (D : Factor S) {f : S.X → ℝ} {C : ℝ}
    (hm : Measurable f) (hb : ∀ x, |f x| ≤ C) (hcond : S.m[f|D.σ] =ᵐ[S.m] 0) {θ : Torus}
    (hθ : specMeasure (prodSystem D).koopman
      (toLpC (prodSystem D) (measurable_tensorSq hm) (abs_tensorSq_le hb)) {θ} ≠ 0) :
    ∃ w : Lp ℂ 2 (prodSystem D).m, w ≠ 0 ∧
      (prodSystem D).koopman w = fourier 1 θ • w ∧
      ∀ g : Lp ℂ 2 (prodSystem D).m, IsTensorD D g → inner ℂ g w = 0 := by
  set U := (prodSystem D).koopman with hU
  set G := toLpC (prodSystem D) (measurable_tensorSq hm) (abs_tensorSq_le hb) with hG
  obtain ⟨w, hw0, hwe, hwmem⟩ := exists_eigenvector_mem_closure_span_of_atom
    (hasSpectralMeasure_specMeasure U G) hθ
  refine ⟨w, hw0, hwe, fun g hg => ?_⟩
  have hperp : ∀ n : ℤ, inner ℂ g ((U ^ n) G) = 0 := by
    intro n
    have h1 : inner ℂ ((U ^ (-n)) g) G = 0 :=
      inner_tensorSq_eq_zero D hm hb hcond (isTensorD_koopman_zpow D hg (-n))
    have h2 := (U ^ n).inner_map_map ((U ^ (-n)) g) G
    have h3 : (U ^ n) ((U ^ (-n)) g) = g := by
      change (U ^ n * U ^ (-n)) g = g
      rw [← zpow_add, add_neg_cancel, zpow_zero]
      rfl
    rw [h3, h1] at h2
    exact h2
  have hle : Submodule.span ℂ (Set.range fun n : ℤ => (U ^ n) G) ≤ (Submodule.span ℂ {g})ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [inner_smul_left, hperp n, mul_zero]
  have := Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _) hwmem
  rw [Submodule.mem_orthogonal] at this
  exact this g (Submodule.mem_span_singleton_self g)

end TensorOrthogonal

end CantorSzemeredi.Proof

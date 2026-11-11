module

public import Mathlib

/-!
# Ergodic decomposition

For a probability-preserving map `T` on a standard Borel space, the conditional measures
`κ y` of `μ` over the `σ`-algebra `I` of almost invariant measurable sets form a Markov kernel
disintegrating `μ` with `κ y` ergodic for almost every `y`.

The proof avoids countable generation of `I`.  Almost invariance of the fibres follows from
`E[g ∘ T | I] = E[g | I]`.  The mean ergodic theorem (Koopman operator on `L²(μ)`, whose fixed
space is `L²(I)` because `I` is the almost invariant `σ`-algebra) gives
`‖A_N 1_G‖₂² → ‖E[1_G | I]‖₂²`; a fibrewise variance computation turns this into
`κ y (s ∩ G) = κ y s * κ y G` for invariant `s` and almost every `y`, for each `G` in a countable
generating `π`-system, which forces `κ y s ∈ {0, 1}`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace CantorSzemeredi.Proof

open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open scoped Topology

namespace ErgodicDecomp

variable {X : Type*} [mX : MeasurableSpace X]

set_option warn.classDefReducibility false in
/-- The σ-algebra of measurable sets that are almost invariant. -/
def aeInv (μ : Measure X) (T : X → X) : MeasurableSpace X where
  MeasurableSet' s := MeasurableSet s ∧ T ⁻¹' s =ᵐ[μ] s
  measurableSet_empty := ⟨MeasurableSet.empty, by simp⟩
  measurableSet_compl s hs := ⟨hs.1.compl, by
    rw [Set.preimage_compl]; exact hs.2.compl⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun i => (hf i).1, by
    rw [Set.preimage_iUnion]; exact EventuallyEqSet.countable_iUnion fun i => (hf i).2⟩

theorem aeInv_le (μ : Measure X) (T : X → X) : aeInv μ T ≤ mX := fun _ hs => hs.1


theorem setIntegral_comp_aeInv {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ)
    {s : Set X} (hs : MeasurableSet[aeInv μ T] s) (g : X → ℝ) (hg : AEStronglyMeasurable g μ) :
    ∫ x in s, g (T x) ∂μ = ∫ x in s, g x ∂μ := by
  obtain ⟨hsm, hTs⟩ := hs
  rw [← integral_indicator hsm, ← integral_indicator hsm]
  have h1 : s.indicator (fun x => g (T x)) =ᵐ[μ] fun x => (s.indicator g) (T x) := by
    filter_upwards [hTs.mem_iff] with x hx
    by_cases h : x ∈ s
    · have : T x ∈ s := hx.2 h
      simp [Set.indicator_of_mem, h, this]
    · have : T x ∉ s := fun h' => h (hx.1 h')
      simp [Set.indicator_of_notMem, h, this]
  rw [integral_congr_ae h1]
  have h2 : AEStronglyMeasurable (s.indicator g) (Measure.map T μ) := by
    rw [hT.map_eq]; exact hg.indicator hsm
  have := integral_map (μ := μ) (φ := T) hT.measurable.aemeasurable h2
  rw [hT.map_eq] at this
  exact this.symm

theorem condExp_comp_aeInv {μ : Measure X} [IsFiniteMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) :
    μ[fun x => g (T x) | aeInv μ T] =ᵐ[μ] μ[g | aeInv μ T] := by
  have hgT : Integrable (fun x => g (T x)) μ := hT.integrable_comp_of_integrable hg
  refine ae_eq_condExp_of_forall_setIntegral_eq (aeInv_le μ T) hg ?_ ?_
    stronglyMeasurable_condExp.aestronglyMeasurable
  · intro s _ _; exact integrable_condExp.integrableOn
  · intro s hs _
    rw [setIntegral_condExp (aeInv_le μ T) hgT hs]
    exact setIntegral_comp_aeInv hT hs g hg.aestronglyMeasurable


/-- A countable generating `π`-system of measurable sets. -/
theorem exists_countable_piSystem (X : Type*) [MeasurableSpace X] [CountablyGenerated X] :
    ∃ P : Set (Set X), P.Countable ∧ IsPiSystem P ∧ (∀ s ∈ P, MeasurableSet s) ∧
      (inferInstance : MeasurableSpace X) = generateFrom P := by
  set G := natGeneratingSequence X
  let finInter (F : Finset ℕ) : Set X := ⋂ i ∈ F, G i
  let P : Set (Set X) := Set.range fun F : {F : Finset ℕ // F.Nonempty} => finInter F.val
  refine ⟨P, Set.countable_range _, ?_, ?_, ?_⟩
  · intro s hs t ht _
    obtain ⟨⟨F, hF⟩, rfl⟩ := hs
    obtain ⟨⟨F', hF'⟩, rfl⟩ := ht
    refine ⟨⟨F ∪ F', hF.mono Finset.subset_union_left⟩, ?_⟩
    ext x; simp only [finInter, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
    constructor
    · intro h; exact ⟨fun i hi => h i (.inl hi), fun i hi => h i (.inr hi)⟩
    · intro ⟨h1, h2⟩ i hi; exact hi.elim (h1 i) (h2 i)
  · intro s hs
    obtain ⟨⟨F, _⟩, rfl⟩ := hs
    exact MeasurableSet.biInter F.countable_toSet fun i _ => measurableSet_natGeneratingSequence i
  · symm
    refine le_antisymm (generateFrom_le fun s hs => ?_) ?_
    · obtain ⟨⟨F, _⟩, rfl⟩ := hs
      exact MeasurableSet.biInter F.countable_toSet fun i _ => measurableSet_natGeneratingSequence i
    · rw [← generateFrom_natGeneratingSequence X]
      exact generateFrom_mono fun s hs => by
        obtain ⟨n, rfl⟩ := hs
        exact ⟨⟨{n}, Finset.singleton_nonempty n⟩, by simp [finInter, G]⟩

section Fibre

variable [StandardBorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)

/-- The conditional measures of `μ` over the almost invariant `σ`-algebra, as a kernel
for the ambient `σ`-algebra. -/
noncomputable def fibre : Kernel X X :=
  Kernel.comap (condExpKernel μ (aeInv μ T)) id (measurable_id'' (aeInv_le μ T))

theorem fibre_apply (y : X) : fibre μ T y = condExpKernel μ (aeInv μ T) y := by
  simp [fibre, Kernel.comap_apply]

instance : IsMarkovKernel (fibre μ T) := by
  unfold fibre; infer_instance

theorem lintegral_fibre {s : Set X} (hs : MeasurableSet s) :
    μ s = ∫⁻ y, fibre μ T y s ∂μ := by
  have h := condExpKernel_comp_trim (μ := μ) (aeInv_le μ T)
  have h1 : μ s = ∫⁻ y, condExpKernel μ (aeInv μ T) y s ∂(μ.trim (aeInv_le μ T)) := by
    conv_lhs => rw [← h]
    rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  rw [h1, lintegral_trim (aeInv_le μ T) (measurable_condExpKernel hs)]
  simp [fibre_apply]

theorem integral_integral_fibre {f : X → ℝ} (hf : Integrable f μ) :
    ∫ y, ∫ x, f x ∂fibre μ T y ∂μ = ∫ x, f x ∂μ := by
  have h := condExp_ae_eq_integral_condExpKernel (aeInv_le μ T) hf
  calc ∫ y, ∫ x, f x ∂fibre μ T y ∂μ = ∫ y, (μ[f | aeInv μ T]) y ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [h] with y hy
        rw [hy, fibre_apply]
    _ = ∫ x, f x ∂μ := integral_condExp (aeInv_le μ T)

variable {μ T}

theorem ae_fibre_real_preimage (hT : MeasurePreserving T μ μ) {B : Set X} (hB : MeasurableSet B) :
    ∀ᵐ y ∂μ, (fibre μ T y).real (T ⁻¹' B) = (fibre μ T y).real B := by
  have h1 := condExpKernel_ae_eq_condExp (μ := μ) (aeInv_le μ T) hB
  have h2 := condExpKernel_ae_eq_condExp (μ := μ) (aeInv_le μ T) (hT.measurable hB)
  have hg : Integrable (B.indicator fun _ => (1 : ℝ)) μ := (integrable_const 1).indicator hB
  have h3 := condExp_comp_aeInv hT hg
  have h4 : (fun x => (B.indicator fun _ => (1 : ℝ)) (T x)) =
      (T ⁻¹' B).indicator fun _ => (1 : ℝ) := by
    ext x; by_cases h : T x ∈ B <;> simp [h]
  rw [h4] at h3
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  rw [fibre_apply]
  exact hy2.trans (hy3.trans hy1.symm)

theorem ae_map_fibre (hT : MeasurePreserving T μ μ) :
    ∀ᵐ y ∂μ, Measure.map T (fibre μ T y) = fibre μ T y := by
  obtain ⟨P, hPc, hPpi, hPm, hPgen⟩ := exists_countable_piSystem X
  have h_ae : ∀ᵐ y ∂μ, ∀ s ∈ P, (fibre μ T y).real (T ⁻¹' s) = (fibre μ T y).real s := by
    rw [ae_ball_iff hPc]
    exact fun s hs => ae_fibre_real_preimage hT (hPm s hs)
  filter_upwards [h_ae] with y hy
  refine ext_of_generate_finite P hPgen hPpi ?_ ?_
  · intro s hs
    rw [Measure.map_apply hT.measurable (hPm s hs)]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (hy s hs)
  · rw [Measure.map_apply hT.measurable .univ, Set.preimage_univ]

end Fibre


section MeanErgodic

variable {μ : Measure X} {T : X → X}

theorem measurable_aeInv_of_ae_comp {f : X → ℝ} (hf : Measurable f) (h : ∀ᵐ x ∂μ, f (T x) = f x) :
    Measurable[aeInv μ T] f := by
  refine measurable_of_Iio fun q => ⟨hf measurableSet_Iio, ?_⟩
  filter_upwards [h] with x hx
  simp only [Set.mem_preimage, Set.mem_Iio, hx]

theorem ae_comp_eq_of_measurable_aeInv {f : X → ℝ} (hf : Measurable[aeInv μ T] f) :
    ∀ᵐ x ∂μ, f (T x) = f x := by
  have h : ∀ q : ℚ, ∀ᵐ x ∂μ, (f (T x) < q ↔ f x < q) := by
    intro q
    have := (hf (measurableSet_Iio (a := (q : ℝ)))).2.mem_iff
    filter_upwards [this] with x hx
    exact hx
  rw [← ae_all_iff] at h
  filter_upwards [h] with x hx
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    exact absurd ((hx q).1 hq1) (not_lt.2 hq2.le)
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    exact absurd ((hx q).2 hq1) (not_lt.2 hq2.le)


/-- The Koopman operator on `L²`. -/
noncomputable def koopman (hT : MeasurePreserving T μ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap

theorem koopman_apply (hT : MeasurePreserving T μ μ) (g : Lp ℝ 2 μ) :
    koopman hT g = Lp.compMeasurePreserving T hT g := rfl

theorem norm_koopman_le (hT : MeasurePreserving T μ μ) : ‖koopman hT‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

theorem coeFn_koopman (hT : MeasurePreserving T μ μ) (g : Lp ℝ 2 μ) :
    (koopman hT g : X → ℝ) =ᵐ[μ] (g : X → ℝ) ∘ T :=
  Lp.coeFn_compMeasurePreserving g hT

theorem coeFn_koopman_iterate (hT : MeasurePreserving T μ μ) (n : ℕ) (g : Lp ℝ 2 μ) :
    (((koopman hT)^[n] g : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ] (g : X → ℝ) ∘ T^[n] := by
  induction n with
  | zero => exact Filter.EventuallyEq.rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine (coeFn_koopman hT _).trans ?_
    have := hT.quasiMeasurePreserving.ae_eq_comp ih
    rw [Function.iterate_succ]
    exact this

theorem coeFn_birkhoffAverage_koopman (hT : MeasurePreserving T μ μ) (N : ℕ) (g : Lp ℝ 2 μ) :
    ((birkhoffAverage ℝ (koopman hT) _root_.id N g : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] fun x => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, (g : X → ℝ) (T^[i] x) := by
  have hsum : ∀ s : Finset ℕ, ((∑ i ∈ s, (koopman hT)^[i] g : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] fun x => ∑ i ∈ s, (g : X → ℝ) (T^[i] x) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero ℝ 2 μ
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine (Lp.coeFn_add _ _).trans ?_
      filter_upwards [ih, coeFn_koopman_iterate hT a g] with x hx1 hx2
      rw [Finset.sum_insert ha, Pi.add_apply, hx1, hx2]; rfl
  unfold birkhoffAverage birkhoffSum
  simp only [_root_.id_eq]
  refine (Lp.coeFn_smul _ _).trans ?_
  filter_upwards [hsum (Finset.range N)] with x hx
  rw [Pi.smul_apply, hx, smul_eq_mul]


theorem norm_sq_Lp (u : Lp ℝ 2 μ) : ‖u‖ ^ 2 = ∫ x, ((u : X → ℝ) x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [sq]

theorem exists_measurable_aeInv_rep (hT : MeasurePreserving T μ μ) {h : Lp ℝ 2 μ}
    (hfix : koopman hT h = h) : ∃ v : X → ℝ, Measurable[aeInv μ T] v ∧ v =ᵐ[μ] (h : X → ℝ) := by
  have hm := (Lp.aestronglyMeasurable h)
  set v := hm.mk _ with hv
  have hvm : Measurable v := hm.stronglyMeasurable_mk.measurable
  have hve : (h : X → ℝ) =ᵐ[μ] v := hm.ae_eq_mk
  refine ⟨v, measurable_aeInv_of_ae_comp hvm ?_, hve.symm⟩
  have h1 : (h : X → ℝ) ∘ T =ᵐ[μ] (h : X → ℝ) := by
    have := coeFn_koopman hT h
    rw [hfix] at this
    exact this.symm
  have h2 := hT.quasiMeasurePreserving.ae_eq_comp hve
  filter_upwards [h2, h1, hve] with x hx1 hx2 hx3
  simp only [Function.comp_apply] at hx1 hx2
  rw [← hx1, hx2, hx3]

theorem koopman_indicatorConstLp_aeInv (hT : MeasurePreserving T μ μ) [IsFiniteMeasure μ] {s : Set X}
    (hs : MeasurableSet[aeInv μ T] s) :
    koopman hT (indicatorConstLp 2 hs.1 (measure_ne_top μ s) (1 : ℝ)) =
      indicatorConstLp 2 hs.1 (measure_ne_top μ s) (1 : ℝ) := by
  refine Lp.ext ?_
  have h1 := coeFn_koopman hT (indicatorConstLp 2 hs.1 (measure_ne_top μ s) (1 : ℝ))
  have h2 : (indicatorConstLp 2 hs.1 (measure_ne_top μ s) (1 : ℝ) : X → ℝ) =ᵐ[μ]
      s.indicator fun _ => (1 : ℝ) := indicatorConstLp_coeFn
  have h3 := hT.quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h3, h2, hs.2.mem_iff] with x hx1 hx2 hx3 hx4
  rw [hx1, Function.comp_apply, hx3]
  simp only [Function.comp_apply] at hx2
  rw [hx2]
  by_cases hx : x ∈ s
  · have : T x ∈ s := hx4.2 hx
    simp [hx, this]
  · have : T x ∉ s := fun h => hx (hx4.1 h)
    simp [hx, this]


omit mX in
theorem birkhoffAverage_apply_eq (φ : X → ℝ) (N : ℕ) (x : X) :
    birkhoffAverage ℝ T φ N x = (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, φ (T^[i] x) := by
  simp [birkhoffAverage, birkhoffSum]

/-- Mean ergodic theorem, in the form `‖A_N 1_G‖₂² → ‖E[1_G | I]‖₂²`. -/
theorem tendsto_integral_sq_birkhoff [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {G : Set X} (hG : MeasurableSet G) :
    Tendsto (fun N : ℕ => ∫ x, (birkhoffAverage ℝ T (G.indicator fun _ => (1 : ℝ)) N x) ^ 2 ∂μ)
      atTop (𝓝 (∫ x, (μ[G.indicator fun _ => (1 : ℝ) | aeInv μ T] x) ^ 2 ∂μ)) := by
  set g : Lp ℝ 2 μ := indicatorConstLp 2 hG (measure_ne_top μ G) (1 : ℝ) with hg
  have hgc : (g : X → ℝ) =ᵐ[μ] G.indicator fun _ => (1 : ℝ) := indicatorConstLp_coeFn
  have hmain := ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection (koopman hT)
    (norm_koopman_le hT) g
  set K := (koopman hT).eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) with hK
  set h : Lp ℝ 2 μ := (K.orthogonalProjectionOnto g : Lp ℝ 2 μ) with hh
  have hlim : Tendsto (fun N : ℕ => ‖birkhoffAverage ℝ (koopman hT) _root_.id N g‖ ^ 2) atTop
      (𝓝 (‖h‖ ^ 2)) := ((continuous_norm.tendsto _).comp hmain).pow 2
  -- identify the limit
  have hfix : koopman hT h = h := by
    have := LinearMap.mem_eqLocus.mp (K.orthogonalProjectionOnto g).2
    simpa [hh] using this
  obtain ⟨v, hvm, hve⟩ := exists_measurable_aeInv_rep hT hfix
  have hint : Integrable (G.indicator fun _ => (1 : ℝ)) μ := (integrable_const 1).indicator hG
  have hv : v =ᵐ[μ] μ[G.indicator fun _ => (1 : ℝ) | aeInv μ T] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (aeInv_le μ T) hint ?_ ?_
      (hvm.stronglyMeasurable.aestronglyMeasurable)
    · intro s _ _
      exact ((Lp.memLp h).integrable one_le_two).congr hve.symm |>.integrableOn
    · intro s hs _
      have hmem : indicatorConstLp 2 hs.1 (measure_ne_top μ s) (1 : ℝ) ∈ K := by
        simp [hK, LinearMap.mem_eqLocus, koopman_indicatorConstLp_aeInv hT hs]
      have hinner := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
        (⟨_, hmem⟩ : K) g
      have h1 : inner ℝ h (indicatorConstLp 2 hs.1 (measure_ne_top μ s) (1 : ℝ)) =
          inner ℝ g (indicatorConstLp 2 hs.1 (measure_ne_top μ s) (1 : ℝ)) := by
        rw [Submodule.coe_inner] at hinner
        exact hinner
      calc ∫ x in s, v x ∂μ = ∫ x in s, (h : X → ℝ) x ∂μ :=
            setIntegral_congr_ae hs.1 (by filter_upwards [hve] with x hx _; exact hx)
        _ = inner ℝ (indicatorConstLp 2 hs.1 (measure_ne_top μ s) (1 : ℝ)) h :=
            (L2.inner_indicatorConstLp_one hs.1 _ h).symm
        _ = inner ℝ h (indicatorConstLp 2 hs.1 (measure_ne_top μ s) (1 : ℝ)) := real_inner_comm _ _
        _ = inner ℝ g (indicatorConstLp 2 hs.1 (measure_ne_top μ s) (1 : ℝ)) := h1
        _ = inner ℝ (indicatorConstLp 2 hs.1 (measure_ne_top μ s) (1 : ℝ)) g := real_inner_comm _ _
        _ = ∫ x in s, (g : X → ℝ) x ∂μ := L2.inner_indicatorConstLp_one hs.1 _ g
        _ = ∫ x in s, G.indicator (fun _ => (1 : ℝ)) x ∂μ :=
            setIntegral_congr_ae hs.1 (by filter_upwards [hgc] with x hx _; exact hx)
  have e1 : ∀ N : ℕ, ‖birkhoffAverage ℝ (koopman hT) _root_.id N g‖ ^ 2 =
      ∫ x, (birkhoffAverage ℝ T (G.indicator fun _ => (1 : ℝ)) N x) ^ 2 ∂μ := by
    intro N
    rw [norm_sq_Lp]
    refine integral_congr_ae ?_
    have hall : ∀ᵐ x ∂μ, ∀ i : ℕ, (g : X → ℝ) (T^[i] x) = G.indicator (fun _ => (1 : ℝ)) (T^[i] x) :=
      ae_all_iff.2 fun i => (hT.iterate i).quasiMeasurePreserving.ae_eq_comp hgc
    filter_upwards [coeFn_birkhoffAverage_koopman hT N g, hall] with x hx1 hx2
    rw [hx1, birkhoffAverage_apply_eq]
    simp only [hx2]
  have e2 : ‖h‖ ^ 2 = ∫ x, (μ[G.indicator fun _ => (1 : ℝ) | aeInv μ T] x) ^ 2 ∂μ := by
    rw [norm_sq_Lp]
    refine integral_congr_ae ?_
    filter_upwards [hve, hv] with x hx1 hx2
    rw [← hx1, hx2]
  simpa only [e1, e2] using hlim

end MeanErgodic


section Fibrewise

variable {ν : Measure X} {T : X → X}

/-- Birkhoff averages of an indicator function. -/
noncomputable abbrev avg (T : X → X) (G : Set X) (N : ℕ) (x : X) : ℝ :=
  birkhoffAverage ℝ T (G.indicator fun _ => (1 : ℝ)) N x

theorem measurable_avg (hT : Measurable T) {G : Set X} (hG : MeasurableSet G) (N : ℕ) :
    Measurable (avg T G N) := by
  have : avg T G N = fun x => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
      (G.indicator fun _ => (1 : ℝ)) (T^[i] x) := by
    funext x; exact birkhoffAverage_apply_eq _ N x
  rw [this]
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
  exact (measurable_const.indicator hG).comp (hT.iterate i)

theorem avg_nonneg (G : Set X) (N : ℕ) (x : X) : 0 ≤ avg T G N x := by
  unfold avg; rw [birkhoffAverage_apply_eq]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem avg_le_one (G : Set X) {N : ℕ} (hN : N ≠ 0) (x : X) : avg T G N x ≤ 1 := by
  unfold avg; rw [birkhoffAverage_apply_eq]
  have h1 : ∑ i ∈ Finset.range N, (G.indicator fun _ => (1 : ℝ)) (T^[i] x) ≤ N := by
    calc _ ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Set.indicator_le_self' (fun _ _ => zero_le_one) _
      _ = N := by simp
  have hN' : (0 : ℝ) < N := by positivity
  calc (N : ℝ)⁻¹ * _ ≤ (N : ℝ)⁻¹ * N := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 := inv_mul_cancel₀ hN'.ne'

theorem integral_comp_iterate (hν : MeasurePreserving T ν ν) (i : ℕ) {φ : X → ℝ}
    (hφ : AEStronglyMeasurable φ ν) : ∫ x, φ (T^[i] x) ∂ν = ∫ x, φ x ∂ν := by
  have h2 : AEStronglyMeasurable φ (Measure.map T^[i] ν) := by
    rw [(hν.iterate i).map_eq]; exact hφ
  have := integral_map (hν.iterate i).measurable.aemeasurable h2
  rw [(hν.iterate i).map_eq] at this
  exact this.symm

theorem integral_avg [IsProbabilityMeasure ν] (hν : MeasurePreserving T ν ν) {G : Set X}
    (hG : MeasurableSet G) {N : ℕ} (hN : N ≠ 0) :
    ∫ x, avg T G N x ∂ν = ν.real G := by
  have : avg T G N = fun x => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
      (G.indicator fun _ => (1 : ℝ)) (T^[i] x) := by
    funext x; exact birkhoffAverage_apply_eq _ N x
  rw [this, integral_const_mul, integral_finsetSum]
  · have hi : ∀ i ∈ Finset.range N, ∫ x, (G.indicator fun _ => (1 : ℝ)) (T^[i] x) ∂ν = ν.real G := by
      intro i _
      rw [integral_comp_iterate hν i (measurable_const.indicator hG).aestronglyMeasurable,
        integral_indicator_const _ hG]
      simp
    rw [Finset.sum_congr rfl hi]
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    simp [hN']
  · intro i _
    have h0 : Integrable (G.indicator fun _ => (1 : ℝ)) ν := (integrable_const (1 : ℝ)).indicator hG
    exact (hν.iterate i).integrable_comp_of_integrable h0


theorem integrable_of_abs_le [IsFiniteMeasure ν] {φ : X → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) : Integrable φ ν :=
  Integrable.of_bound hφ.aestronglyMeasurable C (ae_of_all _ fun x => by simpa using hC x)

theorem sq_integral_le [IsProbabilityMeasure ν] {φ : X → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) : (∫ x, φ x ∂ν) ^ 2 ≤ ∫ x, φ x ^ 2 ∂ν := by
  have hi : Integrable φ ν := integrable_of_abs_le hφ hC
  have hi2 : Integrable (fun x => φ x ^ 2) ν := by
    refine integrable_of_abs_le (hφ.pow_const 2) (C := C ^ 2) fun x => ?_
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC x) 2
  exact (Even.convexOn_pow (𝕜 := ℝ) even_two).map_integral_le (continuousOn_pow 2) isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hi hi2

omit mX in
theorem mem_iff_iterate {s : Set X} (hsT : T ⁻¹' s = s) (i : ℕ) (x : X) :
    T^[i] x ∈ s ↔ x ∈ s := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have : T (T^[i] x) ∈ s ↔ T^[i] x ∈ s := by
      rw [← Set.mem_preimage, hsT]
    rw [this, ih]

theorem indicator_mul_avg {G s : Set X} (hsT : T ⁻¹' s = s) (N : ℕ) (x : X) :
    s.indicator (fun _ => (1 : ℝ)) x * avg T G N x = avg T (s ∩ G) N x := by
  unfold avg
  rw [birkhoffAverage_apply_eq, birkhoffAverage_apply_eq, mul_left_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have := mem_iff_iterate hsT i x
  by_cases hx : x ∈ s
  · have h2 : T^[i] x ∈ s := this.2 hx
    by_cases hg : T^[i] x ∈ G
    · simp [hx, h2, hg]
    · simp [hx, hg]
  · have h2 : T^[i] x ∉ s := fun h => hx (this.1 h)
    simp [hx, h2]

theorem sq_le_variance [IsProbabilityMeasure ν] (hν : MeasurePreserving T ν ν) {G s : Set X}
    (hG : MeasurableSet G) (hs : MeasurableSet s) (hsT : T ⁻¹' s = s) {N : ℕ} (hN : N ≠ 0) :
    (ν.real (s ∩ G) - ν.real s * ν.real G) ^ 2 ≤
      ∫ x, (avg T G N x) ^ 2 ∂ν - (ν.real G) ^ 2 := by
  set c := ν.real G with hc
  have hTm : Measurable T := hν.measurable
  have hav : Measurable (avg T G N) := measurable_avg hTm hG N
  have hb : ∀ x, |avg T G N x - c| ≤ 1 := by
    have hc0 : 0 ≤ c := measureReal_nonneg
    have hc1 : c ≤ 1 := measureReal_le_one
    intro x
    rw [abs_le]
    have := avg_nonneg (T := T) G N x
    have := avg_le_one (T := T) G hN x
    constructor <;> linarith
  have hav_i : Integrable (avg T G N) ν := integrable_of_abs_le hav (C := 1) fun x => by
    rw [abs_of_nonneg (avg_nonneg G N x)]; exact avg_le_one G hN x
  have hav2_i : Integrable (fun x => (avg T G N x) ^ 2) ν := by
    refine integrable_of_abs_le (hav.pow_const 2) (C := 1) fun x => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    have := avg_nonneg (T := T) G N x
    have := avg_le_one (T := T) G hN x
    nlinarith
  have hsi : Measurable (s.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hs
  set φ : X → ℝ := fun x => s.indicator (fun _ => (1 : ℝ)) x * (avg T G N x - c) with hφ
  have hφm : Measurable φ := hsi.mul (hav.sub measurable_const)
  have hφb : ∀ x, |φ x| ≤ 1 := by
    intro x
    simp only [hφ, abs_mul]
    have h1 : |s.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
      by_cases hx : x ∈ s <;> simp [hx]
    calc _ ≤ 1 * 1 := mul_le_mul h1 (hb x) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hJ := sq_integral_le (ν := ν) hφm hφb
  have hint1 : ∫ x, φ x ∂ν = ν.real (s ∩ G) - ν.real s * c := by
    have e1 : ∀ x, φ x = avg T (s ∩ G) N x - c * s.indicator (fun _ => (1 : ℝ)) x := by
      intro x
      simp only [hφ]
      rw [mul_sub, indicator_mul_avg hsT, mul_comm]
    simp_rw [e1]
    have hi1 : Integrable (avg T (s ∩ G) N) ν :=
      integrable_of_abs_le (measurable_avg hTm (hs.inter hG) N) (C := 1) fun x => by
        rw [abs_of_nonneg (avg_nonneg _ N x)]; exact avg_le_one _ hN x
    have hi2 : Integrable (fun x => c * s.indicator (fun _ => (1 : ℝ)) x) ν :=
      ((integrable_const (1 : ℝ)).indicator hs).const_mul c
    rw [integral_sub hi1 hi2, integral_avg hν (hs.inter hG) hN, integral_const_mul,
      integral_indicator_const _ hs]
    simp [mul_comm]
  have hint2 : ∫ x, φ x ^ 2 ∂ν ≤ ∫ x, (avg T G N x - c) ^ 2 ∂ν := by
    refine integral_mono (integrable_of_abs_le (hφm.pow_const 2) (C := 1) fun x => ?_)
      (integrable_of_abs_le ((hav.sub measurable_const).pow_const 2) (C := 1) fun x => ?_)
      fun x => ?_
    · rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hφb x)
    · rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hb x)
    · simp only [hφ, mul_pow]
      have : s.indicator (fun _ => (1 : ℝ)) x ^ 2 ≤ 1 := by
        by_cases hx : x ∈ s <;> simp [hx]
      exact mul_le_of_le_one_left (sq_nonneg _) this
  have hint3 : ∫ x, (avg T G N x - c) ^ 2 ∂ν = ∫ x, (avg T G N x) ^ 2 ∂ν - c ^ 2 := by
    have e : ∀ x, (avg T G N x - c) ^ 2 = (avg T G N x) ^ 2 - 2 * c * avg T G N x + c ^ 2 := by
      intro x; ring
    simp_rw [e]
    have hi3 : Integrable (fun x => avg T G N x ^ 2 - 2 * c * avg T G N x) ν :=
      hav2_i.sub (hav_i.const_mul (2 * c))
    rw [integral_add hi3 (integrable_const (c ^ 2)),
      integral_sub hav2_i (hav_i.const_mul (2 * c)), integral_const_mul, integral_avg hν hG hN]
    simp
    ring
  rw [hint1] at hJ
  linarith

end Fibrewise


section Main

variable [StandardBorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}

theorem integrable_integral_fibre {f : X → ℝ} (hf : Integrable f μ) :
    Integrable (fun y => ∫ x, f x ∂fibre μ T y) μ := by
  have := hf.integral_condExpKernel (m := aeInv μ T)
  simp_rw [fibre_apply]
  exact this

/-- Almost every fibre measure is "mixing in the mean" against every invariant set. -/
theorem ae_fibre_inter_mul (hT : MeasurePreserving T μ μ) {G : Set X} (hG : MeasurableSet G) :
    ∀ᵐ y ∂μ, ∀ s, MeasurableSet s → T ⁻¹' s = s →
      fibre μ T y (s ∩ G) = fibre μ T y s * fibre μ T y G := by
  set κ := fibre μ T with hκ
  have hTm := hT.measurable
  set c : X → ℝ := μ[G.indicator fun _ => (1 : ℝ) | aeInv μ T] with hc
  set cy : X → ℝ := fun y => (κ y).real G with hcy_def
  have hcy_m : Measurable cy := (Kernel.measurable_coe κ hG).ennreal_toReal
  have hcy_b : ∀ y, |cy y| ≤ 1 := fun y => by
    rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have hcy2_i : Integrable (fun y => cy y ^ 2) μ :=
    integrable_of_abs_le (hcy_m.pow_const 2) (C := 1) fun y => by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hcy_b y)
  have hcy_ae : cy =ᵐ[μ] c := by
    have := condExpKernel_ae_eq_condExp (μ := μ) (aeInv_le μ T) hG
    filter_upwards [this] with y hy
    simpa [hcy_def, hκ, fibre_apply] using hy
  have hinv : ∀ᵐ y ∂μ, MeasurePreserving T (κ y) (κ y) := by
    filter_upwards [ae_map_fibre hT] with y hy
    exact ⟨hTm, hy⟩
  set F : ℕ → X → ℝ := fun N y => (∫ x, (avg T G (N + 1) x) ^ 2 ∂κ y) - cy y ^ 2 with hF
  have hav2_i : ∀ N : ℕ, Integrable (fun x => (avg T G (N + 1) x) ^ 2) μ := by
    intro N
    refine integrable_of_abs_le ((measurable_avg hTm hG (N + 1)).pow_const 2) (C := 1) fun x => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    have := avg_nonneg (T := T) G (N + 1) x
    have := avg_le_one (T := T) G (N := N + 1) (by omega) x
    nlinarith
  have hFi : ∀ N, Integrable (F N) μ := fun N =>
    (integrable_integral_fibre (hav2_i N)).sub hcy2_i
  have hFint : ∀ N, ∫ y, F N y ∂μ =
      ∫ x, (avg T G (N + 1) x) ^ 2 ∂μ - ∫ x, (c x) ^ 2 ∂μ := by
    intro N
    rw [integral_sub (integrable_integral_fibre (hav2_i N)) hcy2_i,
      integral_integral_fibre μ T (hav2_i N)]
    congr 1
    exact integral_congr_ae (hcy_ae.mono fun y hy => by simp [hy])
  have hFnn : ∀ N, 0 ≤ᵐ[μ] F N := by
    intro N
    filter_upwards [hinv] with y hy
    have h1 := integral_avg hy hG (N := N + 1) (by omega)
    have h2 := sq_integral_le (ν := κ y) (measurable_avg hTm hG (N + 1)) (C := 1) fun x => by
      rw [abs_of_nonneg (avg_nonneg G (N + 1) x)]; exact avg_le_one G (by omega) x
    rw [h1] at h2
    simp only [hF, hcy_def]
    simp only [Pi.zero_apply]
    linarith
  have hlim : Tendsto (fun N => ∫ y, F N y ∂μ) atTop (𝓝 0) := by
    have h := ((tendsto_integral_sq_birkhoff hT hG).comp (tendsto_add_atTop_nat 1)).sub_const
      (∫ x, (c x) ^ 2 ∂μ)
    rw [sub_self] at h
    exact h.congr fun N => (hFint N).symm
  have hL1 : Tendsto (fun N => eLpNorm (F N - 0) 1 μ) atTop (𝓝 0) := by
    have : ∀ N, eLpNorm (F N - 0) 1 μ = ENNReal.ofReal (∫ y, F N y ∂μ) := by
      intro N
      rw [sub_zero, eLpNorm_one_eq_lintegral_enorm (hFi N).aestronglyMeasurable,
        ofReal_integral_eq_lintegral_ofReal (hFi N) (hFnn N)]
      refine lintegral_congr_ae ((hFnn N).mono fun y hy => ?_)
      exact Real.enorm_eq_ofReal hy
    simp_rw [this]
    simpa using ENNReal.tendsto_ofReal hlim
  have hmeas : TendstoInMeasure μ F atTop 0 :=
    tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top one_ne_zero ENNReal.one_ne_top hL1
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  filter_upwards [hae, hinv] with y hy1 hy2 s hs hsT
  have hlim_y : Tendsto (fun i => F (ns i) y) atTop (𝓝 0) := by simpa using hy1
  have hbound : ∀ i, ((κ y).real (s ∩ G) - (κ y).real s * (κ y).real G) ^ 2 ≤ F (ns i) y := by
    intro i
    simpa [hF, hcy_def] using sq_le_variance hy2 hG hs hsT (N := ns i + 1) (by omega)
  have h0 : ((κ y).real (s ∩ G) - (κ y).real s * (κ y).real G) ^ 2 ≤ 0 :=
    ge_of_tendsto' hlim_y hbound
  have h1 : (κ y).real (s ∩ G) - (κ y).real s * (κ y).real G = 0 :=
    pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h0 (sq_nonneg _))
  have h2 : (κ y).real (s ∩ G) = (κ y).real s * (κ y).real G := by linarith
  simp only [Measure.real] at h2
  rw [← ENNReal.toReal_mul] at h2
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp h2

end Main

end ErgodicDecomp

open ErgodicDecomp in
/-- **Ergodic decomposition.** -/
theorem exists_ergodic_decomposition
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : MeasureTheory.MeasurePreserving T μ μ) :
    ∃ κ : ProbabilityTheory.Kernel X X, ProbabilityTheory.IsMarkovKernel κ ∧
      (∀ s, MeasurableSet s → μ s = ∫⁻ y, κ y s ∂μ) ∧
      ∀ᵐ y ∂μ, Ergodic T (κ y) := by
  refine ⟨fibre μ T, inferInstance, fun s hs => lintegral_fibre μ T hs, ?_⟩
  obtain ⟨P, hPc, hPpi, hPm, hPgen⟩ := exists_countable_piSystem X
  have hall : ∀ᵐ y ∂μ, ∀ G ∈ P, ∀ s, MeasurableSet s → T ⁻¹' s = s →
      fibre μ T y (s ∩ G) = fibre μ T y s * fibre μ T y G := by
    rw [ae_ball_iff hPc]
    exact fun G hG => ae_fibre_inter_mul hT (hPm G hG)
  filter_upwards [hall, ae_map_fibre hT] with y hy hinv
  have : IsProbabilityMeasure (fibre μ T y) := inferInstance
  refine Ergodic.of_preimage_eq ⟨hT.measurable, hinv⟩ fun s hs hsT => ?_
  have hext : (fibre μ T y).restrict s = (fibre μ T y s) • fibre μ T y := by
    refine ext_of_generate_finite P hPgen hPpi ?_ ?_
    · intro G hG
      rw [Measure.restrict_apply (hPm G hG), Measure.smul_apply, smul_eq_mul, Set.inter_comm, hy G hG s hs hsT,
        mul_comm]
    · simp
  have h2 : fibre μ T y s = fibre μ T y s * fibre μ T y s := by
    have := congrArg (fun m => m s) hext
    simpa [Measure.restrict_apply hs] using this
  have h3 : fibre μ T y s = 0 ∨ fibre μ T y sᶜ = 0 := by
    by_cases h0 : fibre μ T y s = 0
    · exact Or.inl h0
    · right
      have h1 : fibre μ T y s = 1 := by
        have hr : (fibre μ T y s).toReal = (fibre μ T y s).toReal * (fibre μ T y s).toReal := by
          rw [← ENNReal.toReal_mul, ← h2]
        have hne : (fibre μ T y s).toReal ≠ 0 := by
          simp [ENNReal.toReal_eq_zero_iff, h0, measure_ne_top]
        have : (fibre μ T y s).toReal = 1 := by
          have := hr; field_simp at this; linarith
        exact (ENNReal.toReal_eq_one_iff _).1 this
      rw [measure_compl hs (measure_ne_top _ _), h1, measure_univ]
      simp
  exact (Filter.eventuallyEmptyOrUniv_iff').mpr (h3.imp ae_eq_empty.mpr ae_eq_univ.mpr)

end CantorSzemeredi.Proof

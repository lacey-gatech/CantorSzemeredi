/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.CondHS

/-!
# Ergodic decomposition

Blueprint: `blueprint/src/chapter/structure.tex`, Lemma `lem:ergodic-decomposition`.

Given an invertible MPS `(X, 𝒜, m, T)` on a standard Borel space, there is a Markov kernel
`y ↦ μ_y` (the conditional measures of `m` over the invariant σ-algebra) such that:
(i)   `m = ∫ μ_y dm(y)`;
(ii)  for `m`-a.e. `y`, `μ_y` is `T`-invariant;
(iii) for `m`-a.e. `y`, `μ_y` is ergodic.
-/

namespace CantorSzemeredi

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped Classical

namespace MPS

/-! ### The invariant σ-algebra -/

/-- The σ-algebra of `T`-invariant measurable sets: `s` belongs iff `MeasurableSet s` and
`T ⁻¹' s = s`. -/
def invariantMeasurableSpace (S : MPS) : MeasurableSpace S.X where
  MeasurableSet' s := MeasurableSet s ∧ S.T ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, Set.preimage_empty⟩
  measurableSet_compl s hs := ⟨hs.1.compl, by rw [Set.preimage_compl, hs.2]⟩
  measurableSet_iUnion f hf :=
    ⟨MeasurableSet.iUnion fun i => (hf i).1,
     by simp only [Set.preimage_iUnion]; congr 1; ext i x; exact Set.ext_iff.mp (hf i).2 x⟩

theorem invariant_measurableSet_iff {S : MPS} {s : Set S.X} :
    MeasurableSet[invariantMeasurableSpace S] s ↔ (MeasurableSet s ∧ S.T ⁻¹' s = s) :=
  Iff.rfl

/-- The invariant factor. -/
def Factor.invariantSets (S : MPS) : Factor S where
  σ := invariantMeasurableSpace S
  le s hs := hs.1
  invariant s := by
    simp only [invariant_measurableSet_iff]
    constructor
    · intro ⟨hm, hinv⟩
      have hTsurj : Function.Surjective S.T := by
        rw [← S.coe_measurableEquiv]; exact S.measurableEquiv.surjective
      have h1 : S.T ⁻¹' s = s := by
        have := congrArg (S.T '' ·) hinv
        rwa [hTsurj.image_preimage, hTsurj.image_preimage] at this
      exact ⟨h1 ▸ hm, h1⟩
    · intro ⟨hm, hinv⟩
      exact ⟨S.measurable_T hm, by rw [hinv]; exact hinv⟩

/-! ### The ergodic decomposition kernel -/

variable {S : MPS} [StandardBorelSpace S.X]

/-- The ergodic decomposition kernel: the conditional measures of `m` over the invariant
σ-algebra. -/
noncomputable def ergodicKernel (S : MPS) [StandardBorelSpace S.X] : Kernel S.X S.X :=
  condKernel (Factor.invariantSets S)

instance (S : MPS) [StandardBorelSpace S.X] : IsMarkovKernel (ergodicKernel S) := by
  rw [ergodicKernel]; infer_instance

/-! ### (i) Disintegration -/

theorem ergodicKernel_comp_measure : (ergodicKernel S) ∘ₘ S.m = S.m :=
  condKernel_comp_measure (Factor.invariantSets S)

/-! ### I-measurable functions are `T`-invariant -/

theorem eq_comp_T_of_invariant_measurable {f : S.X → ℝ}
    (hf : Measurable[invariantMeasurableSpace S] f) : f ∘ S.T = f := by
  ext x
  have key : ∀ a : ℝ, f (S.T x) ≤ a ↔ f x ≤ a := by
    intro a
    have h := hf (measurableSet_Iic (a := a))
    obtain ⟨_, hinv⟩ := h
    have hmem : x ∈ S.T ⁻¹' (f ⁻¹' Set.Iic a) ↔ x ∈ f ⁻¹' Set.Iic a := by
      rw [hinv]
    simpa [Set.mem_preimage, Set.mem_Iic] using hmem
  exact le_antisymm ((key (f x)).mpr le_rfl) ((key (f (S.T x))).mp le_rfl)

/-! ### (ii) Almost every fibre measure is `T`-invariant -/

/-- For each measurable `B`, the fibre measures assign equal `.real`-values to `B` and `T⁻¹'B`
almost everywhere.  This is the pointwise version before the countable-intersection step. -/
theorem ae_ergodicKernel_preimage_eq {B : Set S.X} (hB : MeasurableSet B) :
    ∀ᵐ y ∂S.m, (ergodicKernel S y).real (S.T ⁻¹' B) = (ergodicKernel S y).real B := by
  set I := Factor.invariantSets S
  set a : S.X → ℝ := B.indicator fun _ => 1
  have h_ind : (S.T ⁻¹' B).indicator (fun _ => (1 : ℝ)) = a ∘ S.T := by
    ext x; simp [a, Set.indicator, Set.mem_preimage]
  have h_int : Integrable a S.m := (integrable_const (1 : ℝ)).indicator hB
  have hmeas : Measurable[I.σ] (S.m[a|I.σ]) := stronglyMeasurable_condExp.measurable
  have hinv : S.m[a|I.σ] ∘ S.T = S.m[a|I.σ] := eq_comp_T_of_invariant_measurable hmeas
  have hcomp := I.condExp_comp h_int
  have hcond_eq : S.m[a|I.σ] =ᵐ[S.m] S.m[(S.T ⁻¹' B).indicator (fun _ => (1 : ℝ))|I.σ] := by
    conv_lhs => rw [hinv.symm]
    exact hcomp.trans (by rw [← h_ind])
  have h1 := condKernel_real_ae_eq I hB
  have h2 := condKernel_real_ae_eq I (S.measurable_T hB)
  filter_upwards [h1, h2, hcond_eq] with y hy1 hy2 hy3
  show (condKernel I y).real (S.T ⁻¹' B) = (condKernel I y).real B
  rw [hy2, ← hy3, ← hy1]

/-- For almost every `y`, `Measure.map T (κ_y) = κ_y`. -/
theorem ae_map_ergodicKernel_eq :
    ∀ᵐ y ∂S.m, Measure.map S.T (ergodicKernel S y) = ergodicKernel S y := by
  set G := natGeneratingSequence S.X
  -- Countable π-system: nonempty finite intersections of generators
  let finInter (F : Finset ℕ) : Set S.X := ⋂ i ∈ F, G i
  let P : Set (Set S.X) := Set.range fun F : {F : Finset ℕ // F.Nonempty} => finInter F.val
  have hP_count : P.Countable := Set.countable_range _
  have hP_pi : IsPiSystem P := by
    intro s hs t ht _
    obtain ⟨⟨F, hF⟩, rfl⟩ := hs
    obtain ⟨⟨F', hF'⟩, rfl⟩ := ht
    refine ⟨⟨F ∪ F', hF.mono Finset.subset_union_left⟩, ?_⟩
    ext x; simp only [finInter, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
    constructor
    · intro h; exact ⟨fun i hi => h i (.inl hi), fun i hi => h i (.inr hi)⟩
    · intro ⟨h1, h2⟩ i hi; exact hi.elim (h1 i) (h2 i)
  have hP_meas : ∀ s ∈ P, MeasurableSet s := by
    intro s hs
    obtain ⟨⟨F, _⟩, rfl⟩ := hs
    exact MeasurableSet.biInter F.countable_toSet fun i _ => measurableSet_natGeneratingSequence i
  have hP_gen : (inferInstance : MeasurableSpace S.X) = generateFrom P := by
    symm
    refine le_antisymm (generateFrom_le fun s hs => hP_meas s hs) ?_
    rw [← generateFrom_natGeneratingSequence S.X]
    exact generateFrom_mono fun s hs => by
      obtain ⟨n, rfl⟩ := hs
      exact ⟨⟨{n}, Finset.singleton_nonempty n⟩, by simp [finInter, G]⟩
  have h_ae : ∀ᵐ y ∂S.m, ∀ s ∈ P,
      (ergodicKernel S y).real (S.T ⁻¹' s) = (ergodicKernel S y).real s := by
    rw [ae_ball_iff hP_count]
    exact fun s hs => ae_ergodicKernel_preimage_eq (hP_meas s hs)
  filter_upwards [h_ae] with y hy
  refine ext_of_generate_finite P hP_gen hP_pi ?_ ?_
  · intro s hs
    have hs_meas : MeasurableSet s := hP_meas s hs
    rw [Measure.map_apply S.measurable_T hs_meas]
    exact (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top _ _) (measure_ne_top _ _)).mp (hy s hs)
  · rw [Measure.map_apply S.measurable_T .univ, Set.preimage_univ]

/-! ### (iii) Almost every fibre measure is ergodic -/

/-- For almost every `y`, the fibre measure `ergodicKernel S y` is ergodic for `T`. -/
theorem ae_ergodic_ergodicKernel :
    ∀ᵐ y ∂S.m, Ergodic S.T (ergodicKernel S y) := by
  set I := Factor.invariantSets S
  haveI : @CountablyGenerated S.X I.σ := sorry
  set G_I := @natGeneratingSequence S.X I.σ _
  let finInterI (F : Finset ℕ) : Set S.X := ⋂ i ∈ F, G_I i
  let P_I : Set (Set S.X) := Set.range fun F : {F : Finset ℕ // F.Nonempty} => finInterI F.val
  have hPI_count : P_I.Countable := Set.countable_range _
  have hPI_pi : IsPiSystem P_I := by
    intro s₁ hs₁ s₂ hs₂ _
    obtain ⟨⟨F, hF⟩, rfl⟩ := hs₁; obtain ⟨⟨F', hF'⟩, rfl⟩ := hs₂
    exact ⟨⟨F ∪ F', hF.mono Finset.subset_union_left⟩, by
      ext x; simp only [finInterI, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
      exact ⟨fun h => ⟨fun i hi => h i (.inl hi), fun i hi => h i (.inr hi)⟩,
             fun ⟨h1, h2⟩ i hi => hi.elim (h1 i) (h2 i)⟩⟩
  have hPI_Imeas : ∀ s ∈ P_I, @MeasurableSet S.X I.σ s := by
    intro s hs; obtain ⟨⟨F, _⟩, rfl⟩ := hs
    exact .biInter F.countable_toSet fun i _ => @measurableSet_natGeneratingSequence S.X I.σ _ i
  have hPI_gen : I.σ = @generateFrom S.X P_I := by
    symm; refine le_antisymm (@generateFrom_le S.X P_I I.σ fun s hs => hPI_Imeas s hs) ?_
    rw [← @generateFrom_natGeneratingSequence S.X I.σ _]
    exact generateFrom_mono fun s hs => by
      obtain ⟨n, rfl⟩ := hs
      exact ⟨⟨{n}, Finset.singleton_nonempty n⟩, by simp [finInterI, G_I]⟩
  have h_ae_real : ∀ᵐ y ∂S.m, ∀ s ∈ P_I,
      (ergodicKernel S y).real s = (s.indicator fun _ => (1 : ℝ)) y := by
    rw [ae_ball_iff hPI_count]
    intro s hs
    have hs_I := hPI_Imeas s hs
    have h_kr := condKernel_real_ae_eq I (I.le _ hs_I)
    rw [condExp_of_stronglyMeasurable I.le
      ((@stronglyMeasurable_const S.X ℝ I.σ _ (1 : ℝ)).indicator hs_I)
      ((integrable_const 1).indicator (I.le _ hs_I))] at h_kr
    exact h_kr
  filter_upwards [ae_map_ergodicKernel_eq (S := S), h_ae_real] with y hy_inv hy_01
  refine Ergodic.of_preimage_eq ⟨S.measurable_T, hy_inv⟩ fun s hs hTs => ?_
  have hs_I : @MeasurableSet S.X I.σ s := invariant_measurableSet_iff.mpr ⟨hs, hTs⟩
  suffices h01 : ergodicKernel S y s = 0 ∨ ergodicKernel S y sᶜ = 0 by
    exact (Filter.eventuallyEmptyOrUniv_iff').mpr (h01.imp ae_eq_empty.mpr ae_eq_univ.mpr)
  exact (induction_on_inter
    (C := fun u _ => ergodicKernel S y u = 0 ∨ ergodicKernel S y uᶜ = 0)
    hPI_gen hPI_pi (Or.inl measure_empty) (fun u hu => by
      have h := hy_01 u hu
      simp only [Measure.real, Set.indicator_apply] at h
      split_ifs at h with hm
      · right
        have h1 : ergodicKernel S y u = 1 := by
          rw [← ENNReal.ofReal_toReal (measure_ne_top (ergodicKernel S y) u), h,
            ENNReal.ofReal_one]
        have h2 := measure_compl (I.le _ (hPI_Imeas u hu))
          (measure_ne_top (ergodicKernel S y) u)
        rw [h1, measure_univ] at h2; simpa using h2
      · left
        rw [← ENNReal.ofReal_toReal (measure_ne_top (ergodicKernel S y) u), h,
          ENNReal.ofReal_zero])
    (fun t htm h => by rw [compl_compl]; exact h.symm)
    (fun f hfd hfm hf => by
      by_cases hall : ∀ i, ergodicKernel S y (f i) = 0
      · left; rw [measure_iUnion hfd (fun i => I.le _ (hfm i))]
        exact ENNReal.tsum_eq_zero.mpr hall
      · right; push Not at hall; obtain ⟨j, hj⟩ := hall
        exact measure_mono_null (Set.compl_subset_compl.mpr (Set.subset_iUnion f j))
          ((hf j).resolve_left hj))) s hs_I

/-! ### The bundled theorem -/

/-- **Lemma `lem:ergodic-decomposition`.** Given an invertible MPS on a standard Borel space,
the ergodic decomposition kernel satisfies:
(i)   `m = ∫ μ_y dm(y)`,
(ii)  for a.e. `y`, `μ_y` is `T`-invariant,
(iii) for a.e. `y`, `μ_y` is ergodic. -/
theorem ergodicDecomposition :
    (ergodicKernel S) ∘ₘ S.m = S.m ∧
    (∀ᵐ y ∂S.m, Ergodic S.T (ergodicKernel S y)) :=
  ⟨ergodicKernel_comp_measure, ae_ergodic_ergodicKernel⟩

end MPS

end CantorSzemeredi

module

public import CantorSzemeredi.Proof.Dichotomy.Defs
public import CantorSzemeredi.Proof.Dichotomy.Glue
public import Mathlib

/-!
# The cut lemma

## Main statement

* `exists_cut_set`: if `f` is bounded measurable and `FibreTB D f x` holds for almost
  every `x`, then for every `η > 0` there is a `D`-set `B` with `iter n ⁻¹' B =ᵐ B` for all
  `n : ℤ`, `m Bᶜ < η`, and `B.indicator f ∈ compactClass D`.

## Proof

The complexity function `ρ_ε` is replaced by its sublevel sets `netSet D f ε r = {ρ_ε ≤ r}`
(`goodNet` is the set where a fixed finite `S' ⊆ ℤ` is an `ε`-net of the orbit).  These are
`D`-sets (`measurableSet_netSet`), a.e. invariant (`ae_mem_netSet_iff`: `S'` is a net at `T x` iff
`S' + 1` is a net at `x`, by `fibreNorm_shift` applied to the countably many bounded functions
`f ∘ iterⁿ - f ∘ iterˢ`), and exhaust the space a.e. by `FibreTB`.  Then `B = ⋂ₖ netSet (1/(k+1))
(rₖ)` and `indicator_mem_compactClass_of_fibre_cover` finishes.  The a.e. invariance of `B` is
first proved for `T` and then extended to `iter n`, `n : ℤ`, by induction in both directions,
using that `T` and `T⁻¹` are measure preserving.
-/

@[expose] public section

namespace CantorSzemeredi.Proof

open MeasureTheory CSZPort CSZPort.MPS Filter

variable {S : MPS} [StandardBorelSpace S.X]

omit [StandardBorelSpace S.X] in
theorem iter_succ_apply' (n : ℤ) (x : S.X) : S.iter (n + 1) x = S.iter n (S.T x) := by
  cases n with
  | ofNat k =>
    change S.T^[k + 1] x = S.T^[k] (S.T x)
    exact Function.iterate_succ_apply S.T k x
  | negSucc k =>
    have h : Int.negSucc k + 1 = -((k : ℕ) : ℤ) := by simp [Int.negSucc_eq]
    rw [h, S.iter_neg_natCast]
    change S.Tinv^[k] x = S.Tinv^[k + 1] (S.T x)
    rw [Function.iterate_succ_apply, S.Tinv_T]

/-- The set of points at which the finite set `S' ⊆ ℤ` is an `ε`-net of the orbit of `f` in the
fibre norm of `D`. -/
def goodNet (D : Factor S) (f : S.X → ℝ) (ε : ℝ) (S' : Finset ℤ) : Set S.X :=
  {x | ∀ n : ℤ, ∃ s ∈ S', fibreNorm D (f ∘ S.iter n - f ∘ S.iter s) x < ε}

/-- `{ρ_ε ≤ r}`: the points at which the orbit of `f` has an `ε`-net inside itself with at most
`r` elements. -/
def netSet (D : Factor S) (f : S.X → ℝ) (ε : ℝ) (r : ℕ) : Set S.X :=
  {x | ∃ S' : Finset ℤ, S'.card ≤ r ∧ x ∈ goodNet D f ε S'}

theorem measurableSet_goodNet (D : Factor S) {f : S.X → ℝ} (hf : Measurable f) (ε : ℝ)
    (S' : Finset ℤ) : MeasurableSet[D.σ] (goodNet D f ε S') := by
  have : goodNet D f ε S' =
      ⋂ n : ℤ, ⋃ s ∈ S', {x | fibreNorm D (f ∘ S.iter n - f ∘ S.iter s) x < ε} := by
    ext x; simp [goodNet]
  rw [this]
  refine MeasurableSet.iInter fun n => MeasurableSet.biUnion S'.countable_toSet fun s _ => ?_
  exact measurable_fibreNorm D ((hf.comp (S.measurable_iter n)).sub
    (hf.comp (S.measurable_iter s))) measurableSet_Iio

theorem measurableSet_netSet (D : Factor S) {f : S.X → ℝ} (hf : Measurable f) (ε : ℝ) (r : ℕ) :
    MeasurableSet[D.σ] (netSet D f ε r) := by
  have : netSet D f ε r = ⋃ S' : Finset ℤ, ⋃ (_ : S'.card ≤ r), goodNet D f ε S' := by
    ext x; simp [netSet]
  rw [this]
  exact MeasurableSet.iUnion fun S' => MeasurableSet.iUnion fun _ => measurableSet_goodNet D hf ε S'

theorem monotone_netSet (D : Factor S) (f : S.X → ℝ) (ε : ℝ) : Monotone (netSet D f ε) :=
  fun _ _ h _ ⟨S', hc, hx⟩ => ⟨S', hc.trans h, hx⟩

/-- The shift identity for all orbit differences simultaneously. -/
theorem ae_fibreNorm_shift_orbit (D : Factor S) {f : S.X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) :
    ∀ᵐ x ∂S.m, ∀ n s : ℤ, fibreNorm D (f ∘ S.iter n - f ∘ S.iter s) (S.T x) =
      fibreNorm D (f ∘ S.iter (n + 1) - f ∘ S.iter (s + 1)) x := by
  rw [ae_all_iff]; intro n
  rw [ae_all_iff]; intro s
  have hm : Measurable (f ∘ S.iter n - f ∘ S.iter s) :=
    (hf.comp (S.measurable_iter n)).sub (hf.comp (S.measurable_iter s))
  have hb : ∀ x, |(f ∘ S.iter n - f ∘ S.iter s) x| ≤ C + C := fun x => by
    simp only [Pi.sub_apply, Function.comp]
    exact (abs_sub _ _).trans (add_le_add (hC _) (hC _))
  filter_upwards [fibreNorm_shift D (memLp_two_of_bounded hm hb)] with x hx
  rw [hx]
  congr 1
  funext y
  simp [Function.comp, iter_succ_apply']

/-- A.e. invariance of the level sets of the complexity function. -/
theorem ae_mem_netSet_iff (D : Factor S) {f : S.X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) :
    ∀ᵐ x ∂S.m, ∀ (ε : ℝ) (r : ℕ), (x ∈ netSet D f ε r ↔ S.T x ∈ netSet D f ε r) := by
  filter_upwards [ae_fibreNorm_shift_orbit D hf hC] with x hx ε r
  classical
  constructor
  · rintro ⟨S'', hc, hS''⟩
    refine ⟨S''.image (· - 1), Finset.card_image_le.trans hc, fun n => ?_⟩
    obtain ⟨s, hs, hlt⟩ := hS'' (n + 1)
    refine ⟨s - 1, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [hx n (s - 1)]
    simpa using hlt
  · rintro ⟨S', hc, hS'⟩
    refine ⟨S'.image (· + 1), Finset.card_image_le.trans hc, fun n => ?_⟩
    obtain ⟨s, hs, hlt⟩ := hS' (n - 1)
    refine ⟨s + 1, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [hx (n - 1) s] at hlt
    simpa using hlt

omit [StandardBorelSpace S.X] in
/-- If `T⁻¹ B =ᵐ B` (pointwise a.e. iff), then `iterⁿ ⁻¹' B =ᵐ B` for all `n : ℤ`. -/
theorem ae_iter_mem_iff_of_ae_T_mem_iff {B : Set S.X} (h : ∀ᵐ x ∂S.m, x ∈ B ↔ S.T x ∈ B)
    (n : ℤ) : ∀ᵐ x ∂S.m, S.iter n x ∈ B ↔ x ∈ B := by
  induction n using Int.induction_on with
  | zero => exact Eventually.of_forall fun x => Iff.rfl
  | succ k ih =>
    have h1 := S.measurePreserving.quasiMeasurePreserving.ae ih
    filter_upwards [h1, h] with x h1 h2
    rw [iter_succ_apply']
    exact h1.trans h2.symm
  | pred k ih =>
    have h0 : ∀ᵐ x ∂S.m, S.iter (-(k : ℤ) - 1) (S.T x) ∈ B ↔ S.T x ∈ B := by
      filter_upwards [ih, h] with x h1 h2
      have e : S.iter (-(k : ℤ)) x = S.iter (-(k : ℤ) - 1) (S.T x) := by
        rw [← iter_succ_apply']; congr 1; ring
      rw [e] at h1
      exact h1.trans h2
    filter_upwards [S.measurePreserving_Tinv.quasiMeasurePreserving.ae h0] with x hx
    rw [S.T_Tinv] at hx
    exact hx

/-- **The cut lemma.**  If `f` is bounded measurable and the orbit of `f` is totally bounded
in the fibre norm at almost every point (`FibreTB`), then for every `η > 0` there is a `D`-set `B`,
a.e. invariant under `iter n` for all `n : ℤ`, with `m Bᶜ < η` and `B.indicator f ∈ compactClass D`.
-/
theorem exists_cut_set (D : Factor S) {f : S.X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hTB : ∀ᵐ x ∂S.m, FibreTB D f x) {η : ℝ} (hη : 0 < η) :
    ∃ B : Set S.X, MeasurableSet[D.σ] B ∧ (∀ n : ℤ, S.iter n ⁻¹' B =ᵐ[S.m] B) ∧
      S.m Bᶜ < ENNReal.ofReal η ∧ B.indicator f ∈ compactClass D := by
  -- scales
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hε
  have hεpos : ∀ k, 0 < ε k := fun k => by simp only [hε]; positivity
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ε := ENNReal.ofReal η) (by simpa using hη) ℕ
  -- choice of `r k`
  have hr : ∀ k : ℕ, ∃ r : ℕ, S.m (netSet D f (ε k) r)ᶜ < (δ k : ENNReal) := by
    intro k
    have hmeas : ∀ r, NullMeasurableSet (netSet D f (ε k) r)ᶜ S.m := fun r =>
      (D.le _ (measurableSet_netSet D hf (ε k) r)).compl.nullMeasurableSet
    have hanti : Antitone fun r => (netSet D f (ε k) r)ᶜ := fun a b hab =>
      Set.compl_subset_compl.2 (monotone_netSet D f (ε k) hab)
    have : IsProbabilityMeasure S.m := S.isProb
    have ht := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
    have h0 : S.m (⋂ r, (netSet D f (ε k) r)ᶜ) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hTB)
      intro hx'
      obtain ⟨S', hS'⟩ := hx' (ε k) (hεpos k)
      exact (Set.mem_iInter.1 hx S'.card) ⟨S', le_rfl, hS'⟩
    rw [h0] at ht
    have hev := (tendsto_order.1 ht).2 (δ k) (by exact_mod_cast hδpos k)
    obtain ⟨r, hr⟩ := hev.exists
    exact ⟨r, hr⟩
  choose r hr using hr
  have hae := ae_mem_netSet_iff D hf hC
  set B : Set S.X := ⋂ k, netSet D f (ε k) (r k) with hB
  have hBmeas : MeasurableSet[D.σ] B :=
    MeasurableSet.iInter fun k => measurableSet_netSet D hf (ε k) (r k)
  have hBT : ∀ᵐ x ∂S.m, x ∈ B ↔ S.T x ∈ B := by
    filter_upwards [hae] with x hx
    simp only [hB, Set.mem_iInter]
    exact forall_congr' fun k => hx (ε k) (r k)
  refine ⟨B, hBmeas, fun n => ?_, ?_, ?_⟩
  · exact Filter.eventuallyEqSet_iff.2 (ae_iter_mem_iff_of_ae_T_mem_iff hBT n)
  · calc S.m Bᶜ = S.m (⋃ k, (netSet D f (ε k) (r k))ᶜ) := by rw [hB, Set.compl_iInter]
      _ ≤ ∑' k, S.m (netSet D f (ε k) (r k))ᶜ := measure_iUnion_le _
      _ ≤ ∑' k, (δ k : ENNReal) := ENNReal.tsum_le_tsum fun k => (hr k).le
      _ < ENNReal.ofReal η := hδsum
  · refine indicator_mem_compactClass_of_fibre_cover D hf hC hBmeas
      (fun n => Filter.eventuallyEqSet_iff.2 (ae_iter_mem_iff_of_ae_T_mem_iff hBT n)) ?_
    intro e he
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt he
    refine ⟨r k, Eventually.of_forall fun x hx => ?_⟩
    obtain ⟨S', hc, hS'⟩ := Set.mem_iInter.1 hx k
    exact ⟨S', hc, fun n => by
      obtain ⟨s, hs, hlt⟩ := hS' n
      exact ⟨s, hs, hlt.trans hk⟩⟩

end CantorSzemeredi.Proof

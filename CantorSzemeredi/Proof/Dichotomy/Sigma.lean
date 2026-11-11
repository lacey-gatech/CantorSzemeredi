module

public import CantorSzemeredi.Proof.Dichotomy.Defs
public import CantorSzemeredi.Proof.Dichotomy.Glue
public import CantorSzemeredi.Proof.Dichotomy.Class
public import Mathlib

/-!
# The σ-algebra of compact sets

**Definition of `E`.**  `NearCompact D f` says that `f` lies in the `L²(m)`-closure of
`compactClass D` (the class 𝔄): for every `ε > 0` there is `g ∈ 𝔄` with
`‖f - g‖₂ ≤ ε`.  The factor `compactFactor D` has underlying σ-algebra
`compactSigma D` whose measurable sets are the **genuinely measurable** sets `B` (for the
ambient σ-algebra, no null-set quotient) with `NearCompact D (1_B)`.

Choices:

* Using exact measurable sets (rather than "a.e. equal to a set with this property") makes
  `E.σ ≤ S.measurableSpace` immediate, and makes the factor axiom `T⁻¹ E = E` hold *exactly*:
  `1_{T⁻¹ B} = 1_B ∘ T`, `𝔄` is stable under `∘ T^{±1}` (`compactClass_comp_T`,
  `compactClass_comp_Tinv`) and `T` preserves `m`.
* The `σ`-algebra axioms: `∅` (the zero function is in 𝔄), complements (`1 - ·`), finite
  intersections (products of `[0,1]`-valued clamped approximants), countable unions (finite unions,
  then `L²` convergence `‖1_U - 1_{U_N}‖₂² = m(U ∖ U_N) → 0`).
* `D.σ ≤ (compactFactor D).σ` since indicators of `D`-sets are in 𝔄
  (`compactClass_of_measurable`).
* **For `dichotomy`:** every `g ∈ compactClass D` is `(compactFactor D).σ`-measurable
  (`measurable_of_mem_compactClass`), via `{g > c}`: `1_{g>c}` is the `L²`-limit of
  `clamp(k(g - c), 0, 1) ∈ 𝔄`.  Consequently `g ∘ S.iter n` is `E`-measurable too
  (`measurable_iter_D`), which is the hypothesis of `condCompactZIn_of_condCompactZ`.
* `compactExtension_compactFactor`: `E`-measurable `L²` functions are in the `L²`-closure of
  𝔄 (`nearCompact_of_aestronglyMeasurable`, by `E`-simple functions), and every `g ∈ 𝔄` satisfies
  the ported `CondCompact D E g` (`condCompact_of_mem_compactClass`).
-/

@[expose] public section

namespace CantorSzemeredi.Proof

open MeasureTheory CSZPort CSZPort.MPS Filter Topology
open scoped ENNReal

variable {S : MPS} [StandardBorelSpace S.X]

/-- `f` lies in the `L²(m)`-closure of the class 𝔄 = `compactClass D`. -/
def NearCompact (D : Factor S) (f : S.X → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g ∈ compactClass D, eLpNorm (f - g) 2 S.m ≤ ENNReal.ofReal ε

/-! ### Closure properties of `NearCompact` -/

theorem NearCompact.of_mem {D : Factor S} {f : S.X → ℝ} (hf : f ∈ compactClass D) :
    NearCompact D f := fun ε hε => ⟨f, hf, by simp⟩

theorem compactClass_aestronglyMeasurable {D : Factor S} {g : S.X → ℝ} (hg : g ∈ compactClass D) :
    AEStronglyMeasurable g S.m := hg.1.aestronglyMeasurable

omit [StandardBorelSpace S.X] in
theorem ofReal_half_add {ε : ℝ} (hε : 0 ≤ ε) : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) =
    ENNReal.ofReal ε := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

omit [StandardBorelSpace S.X] in
theorem eLpNorm_sub_le_of_aesm {u v w : S.X → ℝ} (hu : AEStronglyMeasurable u S.m)
    (hv : AEStronglyMeasurable v S.m) (hw : AEStronglyMeasurable w S.m) :
    eLpNorm (u - w) 2 S.m ≤ eLpNorm (u - v) 2 S.m + eLpNorm (v - w) 2 S.m := by
  have := eLpNorm_add_le (p := 2) (μ := S.m) (f := u - v) (g := v - w) (by norm_num)
  simpa [sub_add_sub_cancel] using this

/-- **Closedness.**  If `f` is `L²`-approximable by `NearCompact` functions, it is `NearCompact`. -/
theorem nearCompact_of_approx {D : Factor S} {f : S.X → ℝ} (hf : AEStronglyMeasurable f S.m)
    (h : ∀ ε : ℝ, 0 < ε → ∃ f' : S.X → ℝ, AEStronglyMeasurable f' S.m ∧ NearCompact D f' ∧
      eLpNorm (f - f') 2 S.m ≤ ENNReal.ofReal ε) : NearCompact D f := by
  intro ε hε
  obtain ⟨f', hf', hnc, h1⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨g, hg, h2⟩ := hnc (ε / 2) (half_pos hε)
  refine ⟨g, hg, ?_⟩
  calc eLpNorm (f - g) 2 S.m ≤ eLpNorm (f - f') 2 S.m + eLpNorm (f' - g) 2 S.m :=
        eLpNorm_sub_le_of_aesm hf hf' (compactClass_aestronglyMeasurable hg)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal ε := ofReal_half_add hε.le

theorem NearCompact.add {D : Factor S} {f g : S.X → ℝ} (hf : NearCompact D f)
    (hg : NearCompact D g) (hfm : AEStronglyMeasurable f S.m) (hgm : AEStronglyMeasurable g S.m) :
    NearCompact D (f + g) := by
  intro ε hε
  obtain ⟨a, ha, h1⟩ := hf (ε / 2) (half_pos hε)
  obtain ⟨b, hb, h2⟩ := hg (ε / 2) (half_pos hε)
  refine ⟨fun x => a x + b x, compactClass_add ha hb, ?_⟩
  have hsub : f + g - (fun x => a x + b x) = (f - a) + (g - b) := by
    funext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [hsub]
  calc eLpNorm ((f - a) + (g - b)) 2 S.m ≤ eLpNorm (f - a) 2 S.m + eLpNorm (g - b) 2 S.m :=
        eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal ε := ofReal_half_add hε.le

theorem NearCompact.const_mul {D : Factor S} {f : S.X → ℝ} (hf : NearCompact D f) (c : ℝ) :
    NearCompact D (fun x => c * f x) := by
  intro ε hε
  have hc : (0 : ℝ) < |c| + 1 := by positivity
  obtain ⟨a, ha, h1⟩ := hf (ε / (|c| + 1)) (div_pos hε hc)
  refine ⟨fun x => c * a x, compactClass_smul ha c, ?_⟩
  have hsub : (fun x => c * f x) - (fun x => c * a x) = c • (f - a) := by
    funext x; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hsub, eLpNorm_const_smul]
  calc ‖c‖ₑ * eLpNorm (f - a) 2 S.m ≤ ‖c‖ₑ * ENNReal.ofReal (ε / (|c| + 1)) :=
        mul_le_mul_right h1 _
    _ = ENNReal.ofReal (|c| * (ε / (|c| + 1))) := by
        rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_mul (abs_nonneg c)]
    _ ≤ ENNReal.ofReal ε := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_div_assoc, div_le_iff₀ hc]; nlinarith [abs_nonneg c]

theorem NearCompact.comp_T {D : Factor S} {f : S.X → ℝ} (hf : NearCompact D f)
    (hfm : AEStronglyMeasurable f S.m) : NearCompact D (f ∘ S.T) := by
  intro ε hε
  obtain ⟨g, hg, h1⟩ := hf ε hε
  refine ⟨g ∘ S.T, compactClass_comp_T hg, ?_⟩
  have : f ∘ S.T - g ∘ S.T = (f - g) ∘ S.T := rfl
  rw [this, eLpNorm_comp_measurePreserving (hfm.sub (compactClass_aestronglyMeasurable hg))
    S.measurePreserving]
  exact h1

theorem NearCompact.comp_Tinv {D : Factor S} {f : S.X → ℝ} (hf : NearCompact D f)
    (hfm : AEStronglyMeasurable f S.m) : NearCompact D (f ∘ S.Tinv) := by
  intro ε hε
  obtain ⟨g, hg, h1⟩ := hf ε hε
  refine ⟨g ∘ S.Tinv, compactClass_comp_Tinv hg, ?_⟩
  have : f ∘ S.Tinv - g ∘ S.Tinv = (f - g) ∘ S.Tinv := rfl
  rw [this, eLpNorm_comp_measurePreserving (hfm.sub (compactClass_aestronglyMeasurable hg))
    S.measurePreserving_Tinv]
  exact h1

/-! ### Indicators -/

/-- Indicator of a set as a real function. -/
noncomputable def ind (B : Set S.X) : S.X → ℝ := B.indicator fun _ => (1 : ℝ)

omit [StandardBorelSpace S.X] in
theorem measurable_ind {B : Set S.X} (hB : MeasurableSet B) : Measurable (ind B) :=
  measurable_const.indicator hB

omit [StandardBorelSpace S.X] in
theorem ind_nonneg_le_one (B : Set S.X) (x : S.X) : 0 ≤ ind B x ∧ ind B x ≤ 1 := by
  by_cases hx : x ∈ B <;> simp [ind, hx]

omit [StandardBorelSpace S.X] in
theorem eLpNorm_ind_le {A : Set S.X} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε)
    (h : S.m A ≤ ENNReal.ofReal (ε ^ 2)) : eLpNorm (ind A) 2 S.m ≤ ENNReal.ofReal ε := by
  unfold ind
  rw [eLpNorm_indicator_const hA.nullMeasurableSet (by norm_num) (by norm_num)]
  simp only [enorm_one, one_mul, ENNReal.toReal_ofNat]
  calc S.m A ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal (ε ^ 2)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        congr 1
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hε.le]

/-- The class of sets whose indicator is in the `L²`-closure of 𝔄. -/
def IsKSet (D : Factor S) (B : Set S.X) : Prop := MeasurableSet B ∧ NearCompact D (ind B)

theorem nearCompact_zero (D : Factor S) : NearCompact D (0 : S.X → ℝ) :=
  NearCompact.of_mem (compactClass_of_measurable (D := D) (g := fun _ => 0)
    measurable_const ⟨0, fun _ => by simp⟩)

theorem const_mem_compactClass (D : Factor S) (c : ℝ) : (fun _ : S.X => c) ∈ compactClass D :=
  compactClass_of_measurable (D := D) measurable_const ⟨|c|, fun _ => le_rfl⟩

theorem IsKSet.empty (D : Factor S) : IsKSet D (∅ : Set S.X) := by
  refine ⟨MeasurableSet.empty, ?_⟩
  have : ind (∅ : Set S.X) = 0 := by funext x; simp [ind]
  rw [this]; exact nearCompact_zero D

theorem IsKSet.compl {D : Factor S} {B : Set S.X} (hB : IsKSet D B) : IsKSet D Bᶜ := by
  refine ⟨hB.1.compl, fun ε hε => ?_⟩
  obtain ⟨g, hg, h1⟩ := hB.2 ε hε
  refine ⟨fun x => 1 - g x, compactClass_sub (const_mem_compactClass D 1) hg, ?_⟩
  have : ind Bᶜ - (fun x => 1 - g x) = -(ind B - g) := by
    funext x
    by_cases hx : x ∈ B <;> simp [ind, hx]
  rw [this, eLpNorm_neg]; exact h1

omit [StandardBorelSpace S.X] in
theorem abs_mul_sub_mul_le {a b a' b' : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (ha' : 0 ≤ a' ∧ a' ≤ 1) (hb' : 0 ≤ b' ∧ b' ≤ 1) :
    |a * b - a' * b'| ≤ |a - a'| + |b - b'| := by
  have : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [this]
  calc |(a - a') * b + a' * (b - b')| ≤ |(a - a') * b| + |a' * (b - b')| := abs_add_le _ _
    _ = |a - a'| * |b| + |a'| * |b - b'| := by rw [abs_mul, abs_mul]
    _ ≤ |a - a'| * 1 + 1 * |b - b'| := by
        gcongr
        · exact abs_le.2 ⟨by linarith [hb.1], hb.2⟩
        · exact abs_le.2 ⟨by linarith [ha'.1], ha'.2⟩
    _ = _ := by ring

/-- Clamped approximants: `1_B` is approximated by `[0,1]`-valued elements of 𝔄. -/
theorem IsKSet.exists_clamp {D : Factor S} {B : Set S.X} (hB : IsKSet D B) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ compactClass D, (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧ eLpNorm (ind B - g) 2 S.m ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hg, h1⟩ := hB.2 ε hε
  refine ⟨fun x => max 0 (min (g x) 1), compactClass_clamp hg 0 1, fun x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩, le_trans ?_ h1⟩
  refine eLpNorm_mono ((measurable_ind hB.1).aestronglyMeasurable.sub
    (compactClass_aestronglyMeasurable (compactClass_clamp hg 0 1))) fun x => ?_
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  obtain ⟨h0, h1'⟩ := ind_nonneg_le_one B x
  have hc : max 0 (min (ind B x) 1) = ind B x := by
    rw [min_eq_left h1', max_eq_right h0]
  have := (lipschitzWith_clamp 0 1).dist_le_mul (ind B x) (g x)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at this
  rw [hc] at this
  exact this

theorem IsKSet.inter {D : Factor S} {A B : Set S.X} (hA : IsKSet D A) (hB : IsKSet D B) :
    IsKSet D (A ∩ B) := by
  refine ⟨hA.1.inter hB.1, fun ε hε => ?_⟩
  obtain ⟨a, ha, ha01, h1⟩ := hA.exists_clamp (half_pos hε)
  obtain ⟨b, hb, hb01, h2⟩ := hB.exists_clamp (half_pos hε)
  refine ⟨fun x => a x * b x, compactClass_mul ha hb, ?_⟩
  have hu : AEStronglyMeasurable (ind A - a) S.m :=
    ((measurable_ind hA.1).aestronglyMeasurable).sub (compactClass_aestronglyMeasurable ha)
  have hv : AEStronglyMeasurable (ind B - b) S.m :=
    ((measurable_ind hB.1).aestronglyMeasurable).sub (compactClass_aestronglyMeasurable hb)
  calc eLpNorm (ind (A ∩ B) - fun x => a x * b x) 2 S.m
      ≤ eLpNorm (fun x => ‖(ind A - a) x‖ + ‖(ind B - b) x‖) 2 S.m := by
        refine eLpNorm_mono ((measurable_ind (hA.1.inter hB.1)).aestronglyMeasurable.sub
          (ha.1.mul hb.1).aestronglyMeasurable) fun x => ?_
        have hind : ind (A ∩ B) x = ind A x * ind B x := by
          by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [ind, hxA, hxB]
        simp only [Pi.sub_apply, Real.norm_eq_abs, hind]
        have := abs_mul_sub_mul_le (ind_nonneg_le_one A x) (ind_nonneg_le_one B x) (ha01 x)
          (hb01 x)
        refine this.trans ?_
        exact le_of_eq (abs_of_nonneg (by positivity)).symm
    _ ≤ eLpNorm (fun x => ‖(ind A - a) x‖) 2 S.m + eLpNorm (fun x => ‖(ind B - b) x‖) 2 S.m :=
        eLpNorm_add_le (by norm_num)
    _ = eLpNorm (ind A - a) 2 S.m + eLpNorm (ind B - b) 2 S.m := by
        rw [eLpNorm_norm _ hu, eLpNorm_norm _ hv]
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal ε := ofReal_half_add hε.le

theorem IsKSet.union {D : Factor S} {A B : Set S.X} (hA : IsKSet D A) (hB : IsKSet D B) :
    IsKSet D (A ∪ B) := by
  have := (hA.compl.inter hB.compl).compl
  simpa [Set.compl_inter, compl_compl] using this

theorem IsKSet.accumulate {D : Factor S} {B : ℕ → Set S.X} (hB : ∀ n, IsKSet D (B n)) (N : ℕ) :
    IsKSet D (Set.accumulate B N) := by
  induction N with
  | zero => simpa [Set.accumulate] using hB 0
  | succ n ih => rw [Set.accumulate_succ]; exact ih.union (hB _)

theorem IsKSet.iUnion {D : Factor S} {B : ℕ → Set S.X} (hB : ∀ n, IsKSet D (B n)) :
    IsKSet D (⋃ n, B n) := by
  have hm : MeasurableSet (⋃ n, B n) := MeasurableSet.iUnion fun n => (hB n).1
  refine ⟨hm, nearCompact_of_approx (measurable_ind hm).aestronglyMeasurable fun ε hε => ?_⟩
  set U := ⋃ n, B n with hU
  have hmono : Monotone (Set.accumulate B) := Set.monotone_accumulate
  have hUacc : ⋃ N, Set.accumulate B N = U := Set.iUnion_accumulate
  have hacc_meas : ∀ N, MeasurableSet (Set.accumulate B N) := fun N => (IsKSet.accumulate hB N).1
  have hlim := tendsto_measure_iUnion_atTop (μ := S.m) hmono
  rw [hUacc] at hlim
  have hδ : (0 : ℝ≥0∞) < ENNReal.ofReal (ε ^ 2) := ENNReal.ofReal_pos.2 (by positivity)
  have hfin : S.m U ≠ ⊤ := measure_ne_top _ _
  have hsub := ENNReal.Tendsto.sub (tendsto_const_nhds (x := S.m U)) hlim (Or.inl hfin)
  rw [tsub_self] at hsub
  obtain ⟨N, hN⟩ := (hsub.eventually (gt_mem_nhds hδ)).exists
  have hsubU : Set.accumulate B N ⊆ U := by
    intro x hx
    obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  have hdiff : S.m (U \ Set.accumulate B N) = S.m U - (S.m ∘ Set.accumulate B) N := by
    rw [measure_diff hsubU (hacc_meas N).nullMeasurableSet (measure_ne_top _ _)]; rfl
  refine ⟨ind (Set.accumulate B N), (measurable_ind (hacc_meas N)).aestronglyMeasurable,
    (IsKSet.accumulate hB N).2, ?_⟩
  have : ind U - ind (Set.accumulate B N) = ind (U \ Set.accumulate B N) := by
    funext x
    by_cases h1 : x ∈ U <;> by_cases h2 : x ∈ Set.accumulate B N <;>
      simp [ind, h1, h2] <;> exact h1 (hsubU h2)
  rw [this]
  exact eLpNorm_ind_le (hm.diff (hacc_meas N)) hε (by rw [hdiff]; exact hN.le)

/-! ### Level sets of elements of 𝔄 -/

theorem isKSet_gt {D : Factor S} {g : S.X → ℝ} (hg : g ∈ compactClass D) (c : ℝ) :
    IsKSet D {x | c < g x} := by
  have hmeas : MeasurableSet {x | c < g x} := measurableSet_lt measurable_const hg.1
  refine ⟨hmeas, nearCompact_of_approx (measurable_ind hmeas).aestronglyMeasurable
    fun ε hε => ?_⟩
  -- the bands `{c < g ≤ c + 1/(k+1)}`
  set band : ℕ → Set S.X := fun k => {x | c < g x ∧ g x ≤ c + 1 / ((k : ℝ) + 1)} with hband
  have hbm : ∀ k, MeasurableSet (band k) := fun k =>
    (measurableSet_lt measurable_const hg.1).inter (measurableSet_le hg.1 measurable_const)
  have hanti : Antitone band := by
    intro i j hij x ⟨h1, h2⟩
    refine ⟨h1, h2.trans ?_⟩
    have : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hij 1
    linarith
  have hinter : ⋂ k, band k = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    by_cases hx : c < g x
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      refine ⟨k, fun h => ?_⟩
      have := h.2
      linarith
    · exact ⟨0, fun h => hx h.1⟩
  have hlim := tendsto_measure_iInter_atTop (μ := S.m) (fun k => (hbm k).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at hlim
  have hδ : (0 : ℝ≥0∞) < ENNReal.ofReal (ε ^ 2) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  have hmem : (fun x => max 0 (min (((k : ℝ) + 1) * (g x - c)) 1)) ∈ compactClass D :=
    compactClass_clamp (compactClass_smul (compactClass_sub hg (const_mem_compactClass D c))
      ((k : ℝ) + 1)) 0 1
  refine ⟨fun x => max 0 (min (((k : ℝ) + 1) * (g x - c)) 1),
    compactClass_aestronglyMeasurable hmem, NearCompact.of_mem hmem, ?_⟩
  refine le_trans (eLpNorm_mono ((measurable_ind hmeas).aestronglyMeasurable.sub
    (compactClass_aestronglyMeasurable hmem)) (g := ind (band k)) fun x => ?_)
    (eLpNorm_ind_le (hbm k) hε hk.le)
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  by_cases h1 : c < g x
  · have hA : ind {x | c < g x} x = 1 := by simp [ind, h1]
    rw [hA]
    by_cases h2 : g x ≤ c + 1 / ((k : ℝ) + 1)
    · have hB : ind (band k) x = 1 := by
        simp [ind, hband, h1]; simpa using h2
      rw [hB]
      have h0 : 0 ≤ max 0 (min (((k : ℝ) + 1) * (g x - c)) 1) := le_max_left _ _
      have h1' : max 0 (min (((k : ℝ) + 1) * (g x - c)) 1) ≤ 1 :=
        max_le zero_le_one (min_le_right _ _)
      rw [abs_of_nonneg (by linarith)]
      simp only [abs_one]
      linarith
    · push_neg at h2
      have h3 : 1 < ((k : ℝ) + 1) * (g x - c) := by
        have : 1 / ((k : ℝ) + 1) < g x - c := by linarith
        rwa [div_lt_iff₀ hk1, mul_comm] at this
      rw [min_eq_right h3.le, max_eq_right zero_le_one]
      simp
  · have hA : ind {x | c < g x} x = 0 := by simp [ind, h1]
    rw [hA]
    push_neg at h1
    have h3 : ((k : ℝ) + 1) * (g x - c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk1.le (by linarith)
    have : max 0 (min (((k : ℝ) + 1) * (g x - c)) 1) = 0 := by
      rw [min_eq_left (h3.trans zero_le_one), max_eq_left h3]
    rw [this]
    simp [ind]

/-! ### The σ-algebra and the factor -/

/-- The σ-algebra of compact sets: measurable sets whose indicator is in the `L²`-closure of 𝔄. -/
def compactSigma (D : Factor S) : MeasurableSpace S.X where
  MeasurableSet' B := IsKSet D B
  measurableSet_empty := IsKSet.empty D
  measurableSet_compl := fun _ h => h.compl
  measurableSet_iUnion := fun _ h => IsKSet.iUnion h

omit [StandardBorelSpace S.X] in
theorem ind_preimage_T (B : Set S.X) : ind (S.T ⁻¹' B) = ind B ∘ S.T := by
  funext x; by_cases h : S.T x ∈ B <;> simp [ind, h]

omit [StandardBorelSpace S.X] in
theorem ind_preimage_Tinv (B : Set S.X) : ind (S.Tinv ⁻¹' B) = ind B ∘ S.Tinv := by
  funext x; by_cases h : S.Tinv x ∈ B <;> simp [ind, h]

theorem IsKSet.preimage_T {D : Factor S} {B : Set S.X} (hB : IsKSet D B) :
    IsKSet D (S.T ⁻¹' B) := by
  refine ⟨S.measurable_T hB.1, ?_⟩
  rw [ind_preimage_T]
  exact hB.2.comp_T (measurable_ind hB.1).aestronglyMeasurable

theorem IsKSet.preimage_Tinv {D : Factor S} {B : Set S.X} (hB : IsKSet D B) :
    IsKSet D (S.Tinv ⁻¹' B) := by
  refine ⟨S.measurable_Tinv hB.1, ?_⟩
  rw [ind_preimage_Tinv]
  exact hB.2.comp_Tinv (measurable_ind hB.1).aestronglyMeasurable

/-- **The factor of compact sets** `E`. -/
def compactFactor (D : Factor S) : Factor S where
  σ := compactSigma D
  le := fun _ hB => hB.1
  invariant := fun B => by
    constructor
    · intro h
      have := h.preimage_Tinv
      have e : S.Tinv ⁻¹' (S.T ⁻¹' B) = B := by ext x; simp
      rwa [e] at this
    · exact fun h => IsKSet.preimage_T h

theorem measurableSet_compactFactor_iff {D : Factor S} {B : Set S.X} :
    MeasurableSet[(compactFactor D).σ] B ↔ MeasurableSet B ∧ NearCompact D (ind B) := Iff.rfl

/-- `compactFactor D` contains `D`. -/
theorem le_compactFactor (D : Factor S) : D.σ ≤ (compactFactor D).σ := by
  intro B hB
  refine ⟨D.le _ hB, NearCompact.of_mem ?_⟩
  refine compactClass_of_measurable (D := D) (g := ind B) ?_ ⟨1, fun x => ?_⟩
  · exact measurable_const.indicator hB
  · have := ind_nonneg_le_one B x
    rw [abs_of_nonneg this.1]; exact this.2

/-- **Elements of 𝔄 are `E`-measurable.**  This is the form used in `dichotomy`. -/
theorem measurable_of_mem_compactClass {D : Factor S} {g : S.X → ℝ} (hg : g ∈ compactClass D) :
    Measurable[(compactFactor D).σ] g := by
  refine measurable_of_Ioi fun c => ?_
  exact isKSet_gt hg c

/-- The orbit of an element of 𝔄 is `E`-measurable. -/
theorem measurable_comp_iter_of_mem_compactClass {D : Factor S} {g : S.X → ℝ}
    (hg : g ∈ compactClass D) (n : ℤ) : Measurable[(compactFactor D).σ] (g ∘ S.iter n) :=
  (measurable_of_mem_compactClass hg).comp (measurable_iter_D (compactFactor D) n)

/-- **Specification of `compactFactor`.**  `E := compactFactor D` is a factor (`T`-invariant
exactly) with
`D.σ ≤ E.σ`, `E.σ ≤` ambient, and every `g ∈ compactClass D` is `E`-measurable. -/
theorem compactFactor_spec (D : Factor S) :
    D.σ ≤ (compactFactor D).σ ∧ (compactFactor D).σ ≤ S.measurableSpace ∧
      (∀ s : Set S.X, MeasurableSet[(compactFactor D).σ] (S.T ⁻¹' s) ↔
        MeasurableSet[(compactFactor D).σ] s) ∧
      ∀ g ∈ compactClass D, Measurable[(compactFactor D).σ] g :=
  ⟨le_compactFactor D, (compactFactor D).le, (compactFactor D).invariant,
    fun _ hg => measurable_of_mem_compactClass hg⟩

/-! ### Density and compact extension -/

/-- Simple functions measurable for a sub-σ-algebra approximate `L²` functions. -/
theorem exists_simpleFunc_trim {α : Type*} {m m0 : MeasurableSpace α} (hm : m ≤ m0)
    (μ : @Measure α m0) [IsFiniteMeasure μ] {f : α → ℝ} (hf : StronglyMeasurable[m] f)
    (hL : MemLp f 2 μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : @SimpleFunc α m ℝ, eLpNorm (f - ⇑s) 2 μ < ε := by
  have hL' : MemLp f 2 (μ.trim hm) := by
    rw [memLp_iff, eLpNorm_trim hm hf]; exact hL
  obtain ⟨s, hs, -⟩ := @MemLp.exists_simpleFunc_eLpNorm_sub_lt α m 2 ℝ _ f (μ.trim hm) hL'
    (by simp) ε hε
  refine ⟨s, ?_⟩
  rwa [eLpNorm_trim hm (hf.sub s.stronglyMeasurable)] at hs

theorem nearCompact_simpleFunc (D : Factor S) (s : @SimpleFunc S.X (compactFactor D).σ ℝ) :
    NearCompact D (⇑s) := by
  have hmeas : ∀ t : @SimpleFunc S.X (compactFactor D).σ ℝ, AEStronglyMeasurable (⇑t) S.m :=
    fun t => ((@SimpleFunc.measurable S.X ℝ (compactFactor D).σ _ t).mono (compactFactor D).le le_rfl).aestronglyMeasurable
  refine @SimpleFunc.induction S.X ℝ (compactFactor D).σ _ (fun t => NearCompact D ⇑t) ?_ ?_ s
  · intro c B hB
    have hB' : IsKSet D B := hB
    have : ⇑(@SimpleFunc.piecewise S.X ℝ (compactFactor D).σ B hB
        (@SimpleFunc.const S.X ℝ (compactFactor D).σ c)
        (@SimpleFunc.const S.X ℝ (compactFactor D).σ 0)) = fun x => c * ind B x := by
      funext x
      by_cases hx : x ∈ B <;> simp [ind, hx, SimpleFunc.piecewise_apply]
    rw [this]
    exact hB'.2.const_mul c
  · intro f g _ hf hg
    show NearCompact D (⇑f + ⇑g)
    exact hf.add hg (hmeas f) (hmeas g)

/-- **Density.**  Every `E`-measurable `L²` function is in the `L²`-closure of 𝔄. -/
theorem nearCompact_of_aestronglyMeasurable (D : Factor S) {f : S.X → ℝ}
    (hf : AEStronglyMeasurable[(compactFactor D).σ] f S.m) (hL : MemLp f 2 S.m) :
    NearCompact D f := by
  refine nearCompact_of_approx hL.aestronglyMeasurable fun ε hε => ?_
  set f' := hf.mk f with hf'
  have hsm : StronglyMeasurable[(compactFactor D).σ] f' := hf.stronglyMeasurable_mk
  have hae : f =ᵐ[S.m] f' := hf.ae_eq_mk
  have hL' : MemLp f' 2 S.m := hL.ae_eq hae
  obtain ⟨s, hs⟩ := exists_simpleFunc_trim (compactFactor D).le S.m hsm hL'
    (ε := ENNReal.ofReal ε) (by simpa using hε)
  refine ⟨⇑s, ((@SimpleFunc.measurable S.X ℝ (compactFactor D).σ _ s).mono (compactFactor D).le le_rfl).aestronglyMeasurable,
    nearCompact_simpleFunc D s, ?_⟩
  have : eLpNorm (f - ⇑s) 2 S.m = eLpNorm (f' - ⇑s) 2 S.m :=
    eLpNorm_congr_ae (hae.sub (Filter.EventuallyEq.refl _ _))
  rw [this]; exact hs.le

/-- Every `g ∈ 𝔄` is conditionally compact over `E` in the ported sense. -/
theorem condCompact_of_mem_compactClass {D : Factor S} {g : S.X → ℝ} (hg : g ∈ compactClass D) :
    CondCompact D (compactFactor D) g := by
  obtain ⟨C, hC⟩ := hg.2.1
  exact (condCompactZIn_of_condCompactZ (le_compactFactor D) hg.1 hC
    (fun n => measurable_comp_iter_of_mem_compactClass hg n) hg.2.2).condCompact
    (compactClass_memLp hg)

/-- `compactFactor D` is a compact extension of `D` (the ported `CompactExtension`). -/
theorem compactExtension_compactFactor (D : Factor S) :
    CompactExtension D (compactFactor D) := by
  intro f hf hL ε hε
  obtain ⟨g, hg, h⟩ := nearCompact_of_aestronglyMeasurable D hf hL ε hε
  exact ⟨g, condCompact_of_mem_compactClass hg, h⟩

end CantorSzemeredi.Proof

module

public import CantorSzemeredi.Proof.Dichotomy.Defs
public import Mathlib

/-!
# Orbit-net gluing

Abstract gluing step of the dichotomy proof.  Nothing
here involves a kernel, an eigenfunction or ergodicity: `f` is any bounded measurable function.

## Main statements

* `exists_orbit_net`: let `f` be measurable with `|f| ≤ C`, `ε : ℝ`, `r : ℕ`, `B` any set,
  and assume that for almost every `x ∈ B` there is a finite `S' ⊂ ℤ`, `|S'| ≤ r`, with
  `∀ n ∃ s ∈ S', fibreNorm D (f ∘ iter n - f ∘ iter s) x < ε` (the orbit of `f` has an
  `ε`-net inside itself at the fibre through `x`).  Then there are `g : Fin r → X → ℝ`, each
  measurable and bounded by `C`, and for every factor `E ≥ D` for which `f ∘ iter s` is
  `E`-measurable for all `s`, `MemModule D E (g q)`, such that
  `∀ n, ∀ᵐ x, x ∈ B → ∃ q, fibreNorm D (f ∘ iter n - g q) x < ε`.
  Each `g q` is the countable `D`-gluing `x ↦ f (iter (c q (κ x)) x)` with `κ : X → ℕ`
  `D`-measurable.  `B` needs no measurability: the sets glued over are the `D`-sets
  `A_k = {x | the k-th finite subset of ℤ is a good net at x}`, and `B` only enters through the
  almost-everywhere hypothesis.
* `exists_orbit_net_of_condCompactZ`: for bounded measurable `f` with
  `CondCompactZ D f`, the same conclusion holds for every `ε > 0`, with `B = univ`
  (net points taken inside the orbit at scale `ε/2`, triangle inequality for `fibreNorm`).
* `condCompactZIn_of_condCompactZ`: `CondCompactZ D f` implies
  `CondCompactZIn D E f` when `D ≤ E` and `f ∘ iter s` is `E`-measurable for all `s`; with
  `CondCompactZIn.condCompact` (Defs) this gives the ported `CondCompact D E f`.
* `indicator_mem_compactClass_of_fibre_cover`: if `B` is a `D`-set with
  `iter n ⁻¹' B =ᵐ B` for all `n : ℤ`, and for every `ε > 0` there is `r` such that a.e. `x ∈ B`
  has an `ε`-net inside the orbit of cardinality `≤ r`, then `B.indicator f ∈ compactClass D`.

## How the later files use it

* `exists_cut_set` (`Cut.lean`): define `ρ_ε`, build the invariant `D`-set
  `B = ⋂_k {ρ_{1/k} ≤ r_k}`, and
  feed `h := fun ε => ⟨r_k, ...⟩` to `indicator_mem_compactClass_of_fibre_cover`.
* `compactExtension_compactFactor` (`Sigma.lean`): for `g ∈ 𝔄` that is `E`-measurable together with
  its orbit, apply
  `condCompactZIn_of_condCompactZ` (or `exists_orbit_net_of_condCompactZ` for the
  `MemModule` form of the approximants).

## The invariant complexity `ρ_ε` worked out on paper

`ρ_ε(x) = min {|S'| : S' ⊂ ℤ finite, ∀ n ∃ s ∈ S', ‖Tⁿf - Tˢf‖_{fibre x} < ε} ∈ ℕ ∪ {∞}`.

1. `D`-measurability: `{ρ_ε ≤ r} = ⋃_{|S'| ≤ r} ⋂_n ⋃_{s ∈ S'} {fibreNorm D (Tⁿf - Tˢf) < ε}`, a
   countable union (`Finset ℤ` is countable) of countable intersections of `D`-sets
   (`measurable_fibreNorm` below).
2. Invariance: by `fibreNorm_shift` applied to the countably many bounded functions
   `Tⁿf - Tˢf`, for a.e. `x`: `‖Tⁿf - Tˢf‖_{fibre (Tx)} = ‖T^{n+1}f - T^{s+1}f‖_{fibre x}` for all
   `n, s : ℤ`.  Hence `S'` is a good net at `Tx` iff `S' + 1` is a good net at `x`
   (`⇐`: given `n`, use `n - 1`; this needs the orbit over `ℤ`).  So `ρ_ε(Tx) = ρ_ε(x)` a.e.
3. Finite a.e. from `FibreTB`; choose `r_k` with `m{ρ_{1/k} > r_k} < η 2^{-k}`;
   `B = ⋂_k {ρ_{1/k} ≤ r_k}` is `D`-measurable, `m(Bᶜ) < η`, and `T⁻¹B =ᵐ B` by step 2
   (`T` measure preserving and invertible gives `iter n ⁻¹' B =ᵐ B` for all `n : ℤ`).
4. `T^n (1_B f) = 1_{T⁻ⁿB} Tⁿf = 1_B Tⁿf` a.e., and on `B` the hypothesis of `exists_orbit_net`
  holds for every
   `ε = 1/k` (as `ρ_{1/k} ≤ r_k`), which is exactly the hypothesis of
   `indicator_mem_compactClass_of_fibre_cover`.

No hole was found: the invariance of `B` is used only to move the indicator through `Tⁿ`, and the
cut set is `D`-measurable so a `D`-set is a union of fibres (`ae_ae_indicator_eq`), which is what
makes the fibre norm of `1_B u` equal `1_B(x) · fibreNorm u x`.
-/

@[expose] public section

namespace CantorSzemeredi.Proof

open MeasureTheory ProbabilityTheory CSZPort CSZPort.MPS

variable {S : MPS} [StandardBorelSpace S.X]

/-! ### Fibre norm API -/

/-- `fibreNorm D g` is `D`-measurable for measurable `g`. -/
theorem measurable_fibreNorm (D : Factor S) {g : S.X → ℝ} (hg : Measurable g) :
    Measurable[D.σ] (fibreNorm D g) := by
  have h1 : StronglyMeasurable fun z => g z ^ 2 := (hg.pow_const 2).stronglyMeasurable
  have h2 : StronglyMeasurable[D.σ] fun x => ∫ z, g z ^ 2 ∂(condKernel D x) :=
    StronglyMeasurable.integral_kernel (κ := condExpKernel S.m D.σ) h1
  exact (Real.continuous_sqrt.comp_stronglyMeasurable h2).measurable

/-- `fibreNorm` only depends on the function up to the fibre measure. -/
theorem fibreNorm_congr_ae (D : Factor S) {g h : S.X → ℝ} {x : S.X}
    (hgh : g =ᵐ[condKernel D x] h) : fibreNorm D g x = fibreNorm D h x := by
  unfold fibreNorm
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hgh] with z hz
  rw [hz]

theorem fibreNorm_sub_comm (D : Factor S) (a b : S.X → ℝ) (x : S.X) :
    fibreNorm D (a - b) x = fibreNorm D (b - a) x := by
  unfold fibreNorm
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.sub_apply]
  ring

/-- Almost everywhere triangle inequality for `fibreNorm` on `L²(m)` functions. -/
theorem fibreNorm_add_le (D : Factor S) {u v : S.X → ℝ} (hu : MemLp u 2 S.m)
    (hv : MemLp v 2 S.m) :
    ∀ᵐ x ∂S.m, fibreNorm D (u + v) x ≤ fibreNorm D u x + fibreNorm D v x := by
  have h := condNorm_add_le D hu hv
  have e1 := condNorm_ae_eq_fibreNorm D (hu.integrable_mul hu)
  have e2 := condNorm_ae_eq_fibreNorm D (hv.integrable_mul hv)
  have e3 := condNorm_ae_eq_fibreNorm D ((hu.add hv).integrable_mul (hu.add hv))
  filter_upwards [h, e1, e2, e3] with x h a b c
  linarith

/-- A function bounded by `C` has fibre norm at most `C` (the fibre measures are probability
measures). -/
theorem fibreNorm_le_of_bound (D : Factor S) {g : S.X → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) (x : S.X) : fibreNorm D g x ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (Classical.arbitrary S.X))
  unfold fibreNorm
  have hint : Integrable (fun y => g y ^ 2) (condKernel D x) :=
    Integrable.mono' (integrable_const (C ^ 2)) ((hg.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by
        simp only [norm_pow, Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC y) 2)
  have h1 : ∫ y, g y ^ 2 ∂(condKernel D x) ≤ C ^ 2 := by
    have := integral_mono hint (integrable_const (C ^ 2)) (fun y =>
      (by
        rw [← sq_abs (g y)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC y) 2 : g y ^ 2 ≤ C ^ 2))
    simpa using this
  calc Real.sqrt (∫ y, g y ^ 2 ∂(condKernel D x)) ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt h1
    _ = C := Real.sqrt_sq hC0

/-! ### Choosing a surjection from `Fin r` onto a small finite set -/

theorem exists_fin_surj (r : ℕ) (F : Finset ℤ) (hF : F.card ≤ r) :
    ∃ c : Fin r → ℤ, ∀ s ∈ F, ∃ q, c q = s := by
  classical
  refine ⟨fun q => if h : (q : ℕ) < F.card then F.orderEmbOfFin rfl ⟨q, h⟩ else 0, ?_⟩
  intro s hs
  have hs' : s ∈ Set.range (F.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hs
  obtain ⟨i, hi⟩ := hs'
  refine ⟨Fin.castLE hF i, ?_⟩
  simp only [Fin.val_castLE, i.isLt, ↓reduceDIte]
  exact hi

/-! ### Measurability of countable gluings -/

omit [StandardBorelSpace S.X] in
theorem measurable_glue {m1 : MeasurableSpace S.X} {κ : S.X → ℕ} (hκ : Measurable[m1] κ)
    {F : ℕ → S.X → ℝ} (hF : ∀ j, Measurable[m1] (F j)) :
    Measurable[m1] (fun x => F (κ x) x) := by
  intro U hU
  have : (fun x => F (κ x) x) ⁻¹' U = ⋃ j, (κ ⁻¹' {j}) ∩ (F j ⁻¹' U) := by
    ext x; simp
  rw [this]
  exact MeasurableSet.iUnion fun j => (hκ (measurableSet_singleton j)).inter (hF j hU)

/-! ### Orbit-net gluing -/

/-- **Orbit-net gluing.**  See the module docstring. -/
theorem exists_orbit_net (D : Factor S) {f : S.X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) {ε : ℝ} (r : ℕ) (B : Set S.X)
    (h : ∀ᵐ x ∂S.m, x ∈ B → ∃ S' : Finset ℤ, S'.card ≤ r ∧
      ∀ n : ℤ, ∃ s ∈ S', fibreNorm D (f ∘ S.iter n - f ∘ S.iter s) x < ε) :
    ∃ g : Fin r → S.X → ℝ, (∀ q, Measurable (g q)) ∧ (∀ q x, |g q x| ≤ C) ∧
      (∀ E : Factor S, D.σ ≤ E.σ → (∀ s : ℤ, Measurable[E.σ] (f ∘ S.iter s)) →
        ∀ q, MemModule D E (g q)) ∧
      ∀ n : ℤ, ∀ᵐ x ∂S.m, x ∈ B → ∃ q : Fin r,
        fibreNorm D (f ∘ S.iter n - g q) x < ε := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat (Finset ℤ)
  -- the `D`-sets `A k`
  let A : ℕ → Set S.X := fun k => {x | (e k).card ≤ r ∧
    ∀ n : ℤ, ∃ s ∈ e k, fibreNorm D (f ∘ S.iter n - f ∘ S.iter s) x < ε}
  have hAm : ∀ k, MeasurableSet[D.σ] (A k) := by
    intro k
    have hfm : ∀ n s : ℤ, Measurable (f ∘ S.iter n - f ∘ S.iter s) := fun n s =>
      (hf.comp (S.measurable_iter n)).sub (hf.comp (S.measurable_iter s))
    have : A k = {x | (e k).card ≤ r} ∩
        ⋂ n : ℤ, ⋃ s ∈ e k, {x | fibreNorm D (f ∘ S.iter n - f ∘ S.iter s) x < ε} := by
      ext x; simp [A]
    rw [this]
    refine (MeasurableSet.const _).inter (MeasurableSet.iInter fun n => ?_)
    exact Finset.measurableSet_biUnion _ fun s _ =>
      measurableSet_lt (measurable_fibreNorm D (hfm n s)) measurable_const
  -- total selector
  let p : ℕ → S.X → Prop := fun k x => x ∈ A k ∨ (k = 0 ∧ x ∉ ⋃ j, A j)
  have htot : ∀ x, ∃ k, p k x := by
    intro x
    by_cases hx : x ∈ ⋃ j, A j
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr ⟨rfl, hx⟩⟩
  have hpm : ∀ k, MeasurableSet[D.σ] {x | p k x} := by
    intro k
    have : {x | p k x} = A k ∪ ({x | k = 0} ∩ (⋃ j, A j)ᶜ) := by
      ext x; simp [p]
    rw [this]
    exact (hAm k).union ((MeasurableSet.const _).inter (MeasurableSet.iUnion hAm).compl)
  let κ : S.X → ℕ := fun x => Nat.find (htot x)
  have hκD : Measurable[D.σ] κ := measurable_find htot hpm
  have hκ_mem : ∀ x, x ∈ (⋃ j, A j) → x ∈ A (κ x) := by
    intro x hx
    rcases Nat.find_spec (htot x) with h1 | ⟨_, h2⟩
    · exact h1
    · exact absurd hx h2
  -- the index selection
  have hc : ∀ j, ∃ c : Fin r → ℤ, (e j).card ≤ r → ∀ s ∈ e j, ∃ q, c q = s := by
    intro j
    by_cases hj : (e j).card ≤ r
    · obtain ⟨c, hc⟩ := exists_fin_surj r (e j) hj
      exact ⟨c, fun _ => hc⟩
    · exact ⟨fun _ => 0, fun h => absurd h hj⟩
  choose cc hcc using hc
  let g : Fin r → S.X → ℝ := fun q x => f (S.iter (cc (κ x) q) x)
  have hgmeas : ∀ (E : Factor S), D.σ ≤ E.σ → (∀ s : ℤ, Measurable[E.σ] (f ∘ S.iter s)) →
      ∀ q, Measurable[E.σ] (g q) := by
    intro E hDE hfE q
    exact measurable_glue (m1 := E.σ) (κ := κ) (F := fun j => f ∘ S.iter (cc j q))
      (hκD.mono hDE le_rfl) (fun j => hfE _)
  have hgmeas0 : ∀ q, Measurable (g q) := by
    intro q
    exact measurable_glue (m1 := S.measurableSpace) (κ := κ)
      (F := fun j => f ∘ S.iter (cc j q)) (hκD.mono D.le le_rfl)
      (fun j => hf.comp (S.measurable_iter _))
  have hgb : ∀ q x, |g q x| ≤ C := fun q x => hC _
  refine ⟨g, hgmeas0, hgb, ?_, ?_⟩
  · intro E hDE hfE q
    refine ⟨?_, memLp_two_of_bounded (hgmeas0 q) (hgb q), ?_⟩
    · exact ⟨g q, (hgmeas E hDE hfE q).stronglyMeasurable, Filter.EventuallyEq.rfl⟩
    · refine ⟨C, ?_⟩
      have := condNorm_ae_eq_fibreNorm D
        ((memLp_two_of_bounded (hgmeas0 q) (hgb q)).integrable_mul
          (memLp_two_of_bounded (hgmeas0 q) (hgb q)))
      filter_upwards [this] with x hx
      rw [hx]
      exact fibreNorm_le_of_bound D (hgmeas0 q) (hgb q) x
  · intro n
    have hZ : ∀ j : ℕ, MeasurableSet[D.σ] (κ ⁻¹' {j}) := fun j =>
      hκD (measurableSet_singleton j)
    have hall : ∀ᵐ x ∂S.m, ∀ j : ℕ, ∀ᵐ z ∂(condKernel D x),
        (κ ⁻¹' {j}).indicator (1 : S.X → ℝ) z = (κ ⁻¹' {j}).indicator (1 : S.X → ℝ) x :=
      ae_all_iff.2 fun j => ae_ae_indicator_eq D (hZ j)
    filter_upwards [h, hall] with x hx hZx hxB
    obtain ⟨S', hcard, hS'⟩ := hx hxB
    obtain ⟨k, rfl⟩ := he S'
    have hxA : x ∈ A (κ x) := hκ_mem x (Set.mem_iUnion.2 ⟨k, hcard, hS'⟩)
    obtain ⟨hcj, hj⟩ := hxA
    obtain ⟨s, hs, hlt⟩ := hj n
    obtain ⟨q, hq⟩ := hcc (κ x) hcj s hs
    refine ⟨q, ?_⟩
    have hz := hZx (κ x)
    have hxz : (κ ⁻¹' {κ x}).indicator (1 : S.X → ℝ) x = 1 := by
      rw [Set.indicator_of_mem (by simp)]; rfl
    have hae : (f ∘ S.iter n - g q) =ᵐ[condKernel D x] (f ∘ S.iter n - f ∘ S.iter s) := by
      filter_upwards [hz] with z hzz
      have hzm : z ∈ κ ⁻¹' {κ x} := by
        by_contra hnot
        rw [Set.indicator_of_notMem hnot, hxz] at hzz
        exact zero_ne_one hzz
      have hκz : κ z = κ x := hzm
      simp only [Pi.sub_apply, Function.comp, g, hκz, hq]
    rw [fibreNorm_congr_ae D hae]
    exact hlt

/-! ### From `CondCompactZ` to net points inside the orbit -/

/-- **Orbit-net form of conditional compactness.**  If `f` is bounded measurable and
`CondCompactZ D f`, then for every `ε > 0` there are finitely many bounded measurable
`D`-gluings `g q` of orbit points of `f`, a net for the whole orbit at scale `ε`. -/
theorem exists_orbit_net_of_condCompactZ (D : Factor S) {f : S.X → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) (hcc : CondCompactZ D f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (g : Fin r → S.X → ℝ), (∀ q, Measurable (g q)) ∧ (∀ q x, |g q x| ≤ C) ∧
      (∀ E : Factor S, D.σ ≤ E.σ → (∀ s : ℤ, Measurable[E.σ] (f ∘ S.iter s)) →
        ∀ q, MemModule D E (g q)) ∧
      ∀ n : ℤ, ∀ᵐ x ∂S.m, ∃ q : Fin r, fibreNorm D (f ∘ S.iter n - g q) x < ε := by
  classical
  obtain ⟨r, g0, hg0, hnet0⟩ := hcc (ε / 2) (half_pos hε)
  have hfn : ∀ n : ℤ, MemLp (f ∘ S.iter n) 2 S.m := fun n =>
    memLp_two_of_bounded (hf.comp (S.measurable_iter n)) (fun x => hC _)
  have htri : ∀ᵐ x ∂S.m, ∀ (n : ℤ) (q : Fin r) (s : ℤ),
      fibreNorm D (f ∘ S.iter n - f ∘ S.iter s) x ≤
        fibreNorm D (f ∘ S.iter n - g0 q) x + fibreNorm D (g0 q - f ∘ S.iter s) x := by
    refine ae_all_iff.2 fun n => ae_all_iff.2 fun q => ae_all_iff.2 fun s => ?_
    have := fibreNorm_add_le D ((hfn n).sub (hg0 q)) ((hg0 q).sub (hfn s))
    filter_upwards [this] with x hx
    rwa [sub_add_sub_cancel] at hx
  have hsec : ∀ᵐ x ∂S.m, ∀ n : ℤ, ∃ q : Fin r,
      fibreNorm D (f ∘ S.iter n - g0 q) x < ε / 2 := ae_all_iff.2 hnet0
  obtain ⟨g, hgm, hgb, hgE, hgnet⟩ := exists_orbit_net D hf hC (ε := ε) r Set.univ (by
    filter_upwards [htri, hsec] with x h1 h2 _
    let sel : Fin r → ℤ := fun q =>
      if hq : ∃ n : ℤ, fibreNorm D (f ∘ S.iter n - g0 q) x < ε / 2 then hq.choose else 0
    refine ⟨Finset.univ.image sel, ?_, ?_⟩
    · exact Finset.card_image_le.trans (by simp)
    · intro n
      obtain ⟨q, hq⟩ := h2 n
      have hex : ∃ n : ℤ, fibreNorm D (f ∘ S.iter n - g0 q) x < ε / 2 := ⟨n, hq⟩
      have hselq : sel q = hex.choose := by simp only [sel, hex, ↓reduceDIte]
      refine ⟨sel q, Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩
      have h3 := h1 n q (sel q)
      have h4 : fibreNorm D (g0 q - f ∘ S.iter (sel q)) x < ε / 2 := by
        rw [fibreNorm_sub_comm, hselq]
        exact hex.choose_spec
      linarith)
  exact ⟨r, g, hgm, hgb, hgE, fun n => by
    filter_upwards [hgnet n] with x hx using hx (Set.mem_univ x)⟩

/-- A bounded measurable `CondCompactZ` function, whose orbit is
`E`-measurable for a factor `E ≥ D`, is `CondCompactZIn D E` (approximants in `L²(E)`, indeed in
the Hilbert module).  Combined with `CondCompactZIn.condCompact` this is the ported
`CondCompact D E f`. -/
theorem condCompactZIn_of_condCompactZ {D E : Factor S} (hDE : D.σ ≤ E.σ) {f : S.X → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (hfE : ∀ s : ℤ, Measurable[E.σ] (f ∘ S.iter s)) (hcc : CondCompactZ D f) :
    CondCompactZIn D E f := by
  intro ε hε
  obtain ⟨r, g, -, -, hgE, hnet⟩ := exists_orbit_net_of_condCompactZ D hf hC hcc hε
  exact ⟨r, g, fun q => (hgE E hDE hfE q).toMemL2, hnet⟩

/-! ### The cut function lies in 𝔄 -/

/-- **Cut function in 𝔄.**  See the module docstring. -/
theorem indicator_mem_compactClass_of_fibre_cover (D : Factor S) {f : S.X → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) {B : Set S.X}
    (hB : MeasurableSet[D.σ] B) (hinv : ∀ n : ℤ, S.iter n ⁻¹' B =ᵐ[S.m] B)
    (h : ∀ ε : ℝ, 0 < ε → ∃ r : ℕ, ∀ᵐ x ∂S.m, x ∈ B → ∃ S' : Finset ℤ, S'.card ≤ r ∧
      ∀ n : ℤ, ∃ s ∈ S', fibreNorm D (f ∘ S.iter n - f ∘ S.iter s) x < ε) :
    B.indicator f ∈ compactClass D := by
  classical
  have hB' : MeasurableSet B := D.le _ hB
  refine ⟨hf.indicator hB', ⟨C, fun x => ?_⟩, ?_⟩
  · by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]; exact hC x
    · rw [Set.indicator_of_notMem hx]
      simpa using (abs_nonneg _).trans (hC x)
  intro ε hε
  obtain ⟨r, hr⟩ := h ε hε
  obtain ⟨g, hgm, hgb, -, hnet⟩ := exists_orbit_net D hf hC (ε := ε) (r + 1) B
    (hr.mono fun x hx hxB => by
      obtain ⟨S', hc, h'⟩ := hx hxB
      exact ⟨S', hc.trans (Nat.le_succ _), h'⟩)
  have hbd : ∀ (q : Fin (r + 1)) (x : S.X), |B.indicator (g q) x| ≤ C := by
    intro q x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]; exact hgb q x
    · rw [Set.indicator_of_notMem hx]
      simpa using (abs_nonneg _).trans (hC x)
  refine ⟨r + 1, fun q => B.indicator (g q), fun q =>
    memLp_two_of_bounded ((hgm q).indicator hB') (hbd q), fun n => ?_⟩
  -- a.e. fibre facts
  have hfm : Measurable (f ∘ S.iter n) := hf.comp (S.measurable_iter n)
  have hae1 : ∀ᵐ z ∂S.m, (B.indicator f ∘ S.iter n) z = B.indicator (f ∘ S.iter n) z := by
    filter_upwards [Filter.eventuallyEqSet_iff.1 (hinv n)] with z hz
    by_cases hzB : z ∈ B
    · have : S.iter n z ∈ B := hz.2 hzB
      simp [Function.comp, Set.indicator_of_mem hzB, Set.indicator_of_mem this]
    · have : S.iter n z ∉ B := fun hh => hzB (hz.1 hh)
      simp [Function.comp, Set.indicator_of_notMem hzB, Set.indicator_of_notMem this]
  have hmeas1 : MeasurableSet {z | (B.indicator f ∘ S.iter n) z = B.indicator (f ∘ S.iter n) z} :=
    measurableSet_eq_fun ((hf.indicator hB').comp (S.measurable_iter n)) (hfm.indicator hB')
  have hfib1 := ae_ae_condKernel D hmeas1 hae1
  have hfib2 := ae_ae_indicator_eq D hB
  filter_upwards [hfib1, hfib2, hnet n] with x h1 h2 h3
  by_cases hxB : x ∈ B
  · obtain ⟨q, hq⟩ := h3 hxB
    refine ⟨q, ?_⟩
    have hae : (B.indicator f ∘ S.iter n - B.indicator (g q)) =ᵐ[condKernel D x]
        (f ∘ S.iter n - g q) := by
      filter_upwards [h1, h2] with z hz1 hz2
      have hzB : z ∈ B := by
        by_contra hnot
        rw [Set.indicator_of_notMem hnot, Set.indicator_of_mem hxB] at hz2
        exact zero_ne_one hz2
      simp only [Pi.sub_apply]
      rw [hz1, Set.indicator_of_mem hzB, Set.indicator_of_mem hzB]
    rw [fibreNorm_congr_ae D hae]
    exact hq
  · refine ⟨⟨0, Nat.succ_pos r⟩, ?_⟩
    have hae : (B.indicator f ∘ S.iter n - B.indicator (g ⟨0, Nat.succ_pos r⟩)) =ᵐ[condKernel D x]
        (0 : S.X → ℝ) := by
      filter_upwards [h1, h2] with z hz1 hz2
      have hzB : z ∉ B := by
        intro hzB
        rw [Set.indicator_of_mem hzB, Set.indicator_of_notMem hxB] at hz2
        exact one_ne_zero hz2
      simp only [Pi.sub_apply]
      rw [hz1, Set.indicator_of_notMem hzB, Set.indicator_of_notMem hzB]
      simp
    rw [fibreNorm_congr_ae D hae]
    simpa [fibreNorm] using hε

end CantorSzemeredi.Proof

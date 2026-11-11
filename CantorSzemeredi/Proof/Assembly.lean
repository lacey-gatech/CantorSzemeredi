module

public import Mathlib
public import CantorSzemeredi.Frozen.CantorSet
public import CantorSzemeredi.Frozen.CantorEnum
public import CantorSzemeredi.Frozen.UpperBanachDensity
public import CantorSzemeredi.Proof.Structure
public import CantorSzemeredi.Proof.Bridge.Cantor
public import CantorSzemeredi.Proof.Bridge.Elementary
public import CantorSzemeredi.Port.Basic
public import CantorSzemeredi.Port.Cantor.Defs
public import CantorSzemeredi.Port.Cantor.Enum
public import CantorSzemeredi.Port.Dynamics.System
public import CantorSzemeredi.Port.Dynamics.Correspondence

/-!
# Assembly of the three theorems from the dichotomy

Conditionally on `DichotomyStatement`, the three frozen theorems (`t:CSZ`, `c:syndetic`,
`t:CSZ-Integers`), with the statements copied verbatim and one extra first binder `hdich`.
-/

@[expose] public section

open MeasureTheory

namespace CantorSzemeredi.Proof

open CantorSzemeredi

/-! ### Bridges -/

/-- The ported Cantor data built from the frozen hypotheses. -/
def cantorDataOf (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hDb' : D.card < b) (hD0 : 0 ∈ D) : CSZPort.CantorData where
  base := b
  digits := D
  three_le_base := hb
  zero_mem := hD0
  digits_lt_base := fun d hd => Finset.mem_range.1 (hDb hd)
  two_le_card := hD2
  card_lt_base := hDb'

theorem cantorDataOf_enum (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hDb' : D.card < b) (hD0 : 0 ∈ D) (n : ℕ) :
    (cantorDataOf b D hb hDb hD2 hDb' hD0).enum n = cantorEnum b D n := by
  set C := cantorDataOf b D hb hDb hD2 hDb' hD0 with hC
  have hdig : ∀ c, c < D.card → C.digit c = cantorDigit D c := by
    intro c hc
    have huniq := Finset.orderEmbOfFin_unique (s := D) (k := D.card) rfl
      (f := fun x : Fin D.card => C.digit x)
      (fun x => C.digit_mem (by simpa [CSZPort.CantorData.delta, hC, cantorDataOf] using x.2))
      (fun x y hxy => C.digit_lt_digit hxy (by
        simpa [CSZPort.CantorData.delta, hC, cantorDataOf] using y.2))
    have := congrFun huniq ⟨c, hc⟩
    simp only [cantorDigit, hc, ↓reduceDIte]
    exact this
  rw [cantorEnum_eq_ofDigits b D hb hDb hD2 hD0 n]
  change Nat.ofDigits b ((Nat.digits D.card n).map C.digit) = _
  congr 1
  refine List.map_congr_left fun c hc => hdig c ?_
  exact Nat.digits_lt_base (by omega) hc

/-- The ported system built from the frozen data. -/
noncomputable def mpsOf {X : Type*} [MeasurableSpace X] (m : Measure X) [IsProbabilityMeasure m]
    (T : X ≃ᵐ X) (hT : MeasurePreserving T m m) : CSZPort.MPS where
  X := X
  m := m
  T := ⇑T
  measurableEquiv := T
  coe_measurableEquiv := rfl
  measurePreserving := hT

/-- A positive uniform liminf gives the frozen uniform lower bound. -/
theorem uniform_bound_of_liminf_pos (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (h : 0 < CSZPort.uniformLiminf a) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℕ, ∀ M N : ℕ, M + L ≤ N →
      c ≤ (∑ n ∈ Finset.Ico M N, a n) / ((N : ℝ) - M) := by
  have hbdd : Filter.IsBoundedUnder (· ≥ ·) CSZPort.uniformFilter
      (fun p : ℕ × ℕ => CSZPort.uniformAvg a p.1 p.2) :=
    ⟨0, Filter.eventually_map.2 (by
      filter_upwards with p
      exact div_nonneg (Finset.sum_nonneg fun n _ => ha n) (Nat.cast_nonneg _))⟩
  have hev := Filter.eventually_lt_of_lt_liminf (half_lt_self h) hbdd
  obtain ⟨L, -, hL⟩ := CSZPort.uniformFilter_hasBasis.eventually_iff.1 hev
  refine ⟨CSZPort.uniformLiminf a / 2, by linarith, L + 1, fun M N hMN => ?_⟩
  have hmem : ((M, N) : ℕ × ℕ) ∈ {p : ℕ × ℕ | L ≤ p.2 - p.1} := by
    simp only [Set.mem_ofPred_eq]; omega
  have := hL hmem
  simp only [CSZPort.uniformAvg] at this
  rw [Nat.cast_sub (by omega)] at this
  exact this.le

/-- The ported upper Banach density equals the frozen one. -/
theorem legacy_ubd_eq (A : Set ℤ) :
    CSZPort.upperBanachDensity A = CantorSzemeredi.upperBanachDensity A := by
  classical
  set g : ℤ × ℤ → ℝ := fun p =>
    (((Finset.Ico p.1 p.2).filter (· ∈ A)).card : ℝ) / (p.2 - p.1 : ℤ) with hg
  have hgr : ∀ M N : ℤ, g (M, N) = ((A ∩ Set.Ico M N).ncard : ℝ) / ((N : ℝ) - M) := by
    intro M N
    have : A ∩ Set.Ico M N = ↑((Finset.Ico M N).filter (· ∈ A)) := by
      ext x; simp [and_comm]
    simp only [hg, this, Set.ncard_coe_finset]
    push_cast
    rfl
  have hev : ∀ a : ℝ, (∀ᶠ p in CSZPort.uniformFilterInt, g p ≤ a) ↔
      ∃ L : ℕ, ∀ p : ℤ × ℤ, (L : ℤ) ≤ p.2 - p.1 → g p ≤ a := by
    intro a
    rw [CSZPort.uniformFilterInt_hasBasis.eventually_iff]
    simp
  have hnn : ∀ a : ℝ, (∀ᶠ p in CSZPort.uniformFilterInt, g p ≤ a) → 0 ≤ a := by
    intro a ha
    obtain ⟨L, hL⟩ := (hev a).1 ha
    have := hL (0, (L : ℤ)) (by simp)
    rw [hgr] at this
    exact le_trans (ubd_ratio_nonneg A 0 L (by simp)) this
  have hmem1 : (1 : ℝ) ∈ {a : ℝ | ∀ᶠ p in CSZPort.uniformFilterInt, g p ≤ a} := by
    refine (hev 1).2 ⟨0, fun p _ => ?_⟩
    rw [show p = (p.1, p.2) from rfl, hgr]; exact ubd_ratio_le_one A _ _
  have hlim : CSZPort.upperBanachDensity A =
      sInf {a : ℝ | ∀ᶠ p in CSZPort.uniformFilterInt, g p ≤ a} := by
    unfold CSZPort.upperBanachDensity
    exact Filter.limsup_eq
  rw [hlim]
  apply le_antisymm
  · refine le_ciInf fun L => ?_
    refine csInf_le ⟨0, fun a ha => hnn a ha⟩ ?_
    refine (hev _).2 ⟨L, fun p hp => ?_⟩
    rw [show p = (p.1, p.2) from rfl, hgr]
    exact ubd_ratio_le_inner A L p.1 p.2 (by omega)
  · refine le_csInf ⟨1, hmem1⟩ fun a ha => ?_
    obtain ⟨L, hL⟩ := (hev a).1 ha
    refine le_trans (ciInf_le ⟨0, by rintro _ ⟨L, rfl⟩; exact ubd_inner_nonneg A L⟩ L) ?_
    refine Real.iSup_le (fun M => Real.iSup_le (fun N => Real.iSup_le (fun h => ?_) ?_) ?_)
      (hnn a ha)
    · have := hL (M, N) (by simp only; omega)
      rwa [hgr] at this
    all_goals exact hnn a ha

/-! ### Target 1 -/

theorem cantor_szemeredi_of_dichotomy (hdich : DichotomyStatement)
    (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hDb' : D.card < b) (hD0 : 0 ∈ D)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    {X : Type*} [MeasurableSpace X] (m : Measure X) [IsProbabilityMeasure m]
    (T : X ≃ᵐ X) (hT : MeasurePreserving T m m)
    (f : X → ℝ) (hf : MemLp f ⊤ m) (hf0 : 0 ≤ᵐ[m] f) (hfne : ¬ f =ᵐ[m] 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℕ, ∀ M N : ℕ, M + L ≤ N →
      c ≤ (∑ n ∈ Finset.Ico M N,
            ∫ x, ∏ j ∈ Finset.range (ℓ + 1), f ((⇑T)^[j * cantorEnum b D n] x) ∂m) /
          ((N : ℝ) - M) := by
  set C := cantorDataOf b D hb hDb hD2 hDb' hD0
  set S := mpsOf m T hT
  have h := csz_functions_all hdich S C 0 ℓ hℓ f hf hf0 hfne
  have hE : ∀ n, C.enum n = cantorEnum b D n := cantorDataOf_enum b D hb hDb hD2 hDb' hD0
  have key : (fun n => ∫ x, ∏ j ∈ Finset.range (ℓ + 1),
      f (S.T^[j * (C.base ^ 0 * C.enum n)] x) ∂S.m) =
      fun n => ∫ x, ∏ j ∈ Finset.range (ℓ + 1), f ((⇑T)^[j * cantorEnum b D n] x) ∂m := by
    funext n
    rw [hE n]
    simp [C, cantorDataOf, S, mpsOf] <;> rfl
  rw [key] at h
  refine uniform_bound_of_liminf_pos _ (fun n => ?_) h
  refine integral_nonneg_of_ae ?_
  have : ∀ j : ℕ, ∀ᵐ x ∂m, 0 ≤ f ((⇑T)^[j * cantorEnum b D n] x) := fun j =>
    (hT.iterate _).quasiMeasurePreserving.ae hf0
  filter_upwards [ae_all_iff.2 this] with x hx
  exact Finset.prod_nonneg fun j _ => hx j

/-! ### Target 2 -/

theorem cantor_szemeredi_syndetic_of_dichotomy (hdich : DichotomyStatement)
    (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hDb' : D.card < b) (hD0 : 0 ∈ D)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    {X : Type*} [MeasurableSpace X] (m : Measure X) [IsProbabilityMeasure m]
    (T : X ≃ᵐ X) (hT : MeasurePreserving T m m)
    (f : X → ℝ) (hf : MemLp f ⊤ m) (hf0 : 0 ≤ᵐ[m] f) (hfne : ¬ f =ᵐ[m] 0) :
    ∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧
      0 < ∫ x, ∏ j ∈ Finset.range (ℓ + 1), f ((⇑T)^[j * cantorEnum b D n] x) ∂m := by
  refine syndetic_of_uniform_avg_pos
    (fun n => ∫ x, ∏ j ∈ Finset.range (ℓ + 1), f ((⇑T)^[j * cantorEnum b D n] x) ∂m)
    (fun n => ?_)
    (cantor_szemeredi_of_dichotomy hdich b D hb hDb hD2 hDb' hD0 ℓ hℓ m T hT f hf hf0 hfne)
  refine integral_nonneg_of_ae ?_
  have : ∀ j : ℕ, ∀ᵐ x ∂m, 0 ≤ f ((⇑T)^[j * cantorEnum b D n] x) := fun j =>
    (hT.iterate _).quasiMeasurePreserving.ae hf0
  filter_upwards [ae_all_iff.2 this] with x hx
  exact Finset.prod_nonneg fun j _ => hx j

/-! ### Target 3 -/

theorem cantor_szemeredi_integers_of_dichotomy (hdich : DichotomyStatement)
    (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hDb' : D.card < b) (hD0 : 0 ∈ D)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (A : Set ℤ) (hA : 0 < upperBanachDensity A) :
    (∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧ 1 ≤ n ∧
      0 < upperBanachDensity {a : ℤ | ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A}) ∧
    ∀ n : ℕ, 1 ≤ n →
      0 < upperBanachDensity {a : ℤ | ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A} →
      0 < cantorEnum b D n ∧ ∃ a : ℤ, ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A := by
  set C := cantorDataOf b D hb hDb hD2 hDb' hD0
  have hE : ∀ n, C.enum n = cantorEnum b D n := cantorDataOf_enum b D hb hDb hD2 hDb' hD0
  have hset : ∀ n, {a : ℤ | ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A} =
      ⋂ j ∈ Finset.range (ℓ + 1), (· + (↑(j * C.enum n) : ℤ)) ⁻¹' A := by
    intro n
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Finset.mem_range, hE n]
    constructor
    · intro h j hj
      have := h j (by omega)
      push_cast; exact this
    · intro h j hj
      have := h j (by omega)
      push_cast at this; exact this
  have hA' : 0 < CSZPort.upperBanachDensity A := by rwa [legacy_ubd_eq]
  have hsynd : ∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧
      0 < upperBanachDensity {a : ℤ | ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A} := by
    obtain ⟨S, B, hBm, hBdens, hBineq⟩ := CSZPort.furstenberg_correspondence A hA'
    have hpos : 0 < S.m B := by
      by_contra h
      have h0 : S.m B = 0 := le_antisymm (not_lt.1 h) (by positivity)
      simp [h0] at hBdens; linarith
    have hS := csz_functions_all hdich S C 0 ℓ hℓ (B.indicator (1 : S.X → ℝ))
      (memLp_top_of_bound (measurable_const.indicator hBm).aestronglyMeasurable 1
        (ae_of_all _ fun x => by
          by_cases hx : x ∈ B <;> simp [Set.indicator, hx]))
      (ae_of_all _ fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
      (by
        intro h
        have : S.m B = 0 := by
          have h1 : S.m {x | B.indicator (1 : S.X → ℝ) x ≠ 0} = 0 := h
          have h2 : {x | B.indicator (1 : S.X → ℝ) x ≠ 0} = B := by
            ext x; by_cases hx : x ∈ B <;> simp [Set.indicator, hx]
          rwa [h2] at h1
        exact hpos.ne' this)
    have hcorr : ∀ n, ∫ x, ∏ j ∈ Finset.range (ℓ + 1),
        (B.indicator (1 : S.X → ℝ)) (S.T^[j * (C.base ^ 0 * C.enum n)] x) ∂S.m =
        S.multiCorr B ℓ (C.enum n) := by
      intro n
      rw [CSZPort.MPS.multiCorr_eq_integral S hBm]
      simp
    simp_rw [hcorr] at hS
    obtain ⟨c, hc, L, hL⟩ := uniform_bound_of_liminf_pos _
      (fun n => CSZPort.MPS.multiCorr_nonneg _ _ _ _) hS
    have hs := syndetic_of_uniform_avg_pos (fun n => S.multiCorr B ℓ (C.enum n))
      (fun n => CSZPort.MPS.multiCorr_nonneg _ _ _ _) ⟨c, hc, L, hL⟩
    refine syndetic_mono (fun n hn => ?_) hs
    rw [hset n, ← legacy_ubd_eq]
    have hR : (⋂ r ∈ (Finset.range (ℓ + 1)).image (fun j : ℕ => (↑(j * C.enum n) : ℤ)),
        (· + r) ⁻¹' A) = ⋂ j ∈ Finset.range (ℓ + 1), (· + (↑(j * C.enum n) : ℤ)) ⁻¹' A := by
      ext x; simp only [Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro h j hj; exact h _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
      · intro h r hr
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
        exact h j hj
    have hR2 : (⋂ r ∈ (Finset.range (ℓ + 1)).image (fun j : ℕ => (↑(j * C.enum n) : ℤ)),
        S.iter r ⁻¹' B) = ⋂ s ∈ Finset.range (ℓ + 1), (S.T^[s * C.enum n]) ⁻¹' B := by
      ext x; simp only [Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro h s hs; exact h _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
      · intro h r hr
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
        exact h s hs
    have := hBineq ((Finset.range (ℓ + 1)).image (fun j : ℕ => (↑(j * C.enum n) : ℤ)))
    rw [hR, hR2] at this
    exact lt_of_lt_of_le hn this
  refine ⟨?_, ?_⟩
  · exact syndetic_one_le hsynd
  · intro n hn hpos
    have hne := upperBanachDensity_pos_nonempty hpos
    refine ⟨cantorEnum_pos b D hb hD2 hD0 hn, ?_⟩
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, ha⟩

end CantorSzemeredi.Proof

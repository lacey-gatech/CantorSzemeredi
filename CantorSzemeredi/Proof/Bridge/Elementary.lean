module

public import Mathlib
public import CantorSzemeredi.Frozen.UpperBanachDensity

/-!
# Elementary bridge lemmas: syndeticity and upper Banach density
-/

@[expose] public section

namespace CantorSzemeredi.Proof

open CantorSzemeredi

/-- Uniformly positive averages force syndetic positivity (Corollary `c:syndetic` from
Theorem `t:CSZ`). -/
theorem syndetic_of_uniform_avg_pos (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (h : ∃ c : ℝ, 0 < c ∧ ∃ L : ℕ, ∀ M N : ℕ, M + L ≤ N →
      c ≤ (∑ n ∈ Finset.Ico M N, a n) / ((N : ℝ) - M)) :
    ∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧ 0 < a n := by
  obtain ⟨c, hc, L, hL⟩ := h
  refine ⟨L, fun n₀ => ?_⟩
  by_contra hcon
  push Not at hcon
  have hz : ∑ n ∈ Finset.Ico n₀ (n₀ + L + 1), a n = 0 :=
    Finset.sum_eq_zero fun n hn => by
      rw [Finset.mem_Ico] at hn
      exact le_antisymm (hcon n hn.1 (by omega)) (ha n)
  have := hL n₀ (n₀ + L + 1) (by omega)
  rw [hz, zero_div] at this
  linarith

/-- Discarding the index `0` from a syndetic set of indices. -/
theorem syndetic_one_le {P : ℕ → Prop}
    (h : ∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧ P n) :
    ∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧ 1 ≤ n ∧ P n := by
  obtain ⟨L, hL⟩ := h
  refine ⟨L + 1, fun n₀ => ?_⟩
  obtain ⟨n, h1, h2, h3⟩ := hL (n₀ + 1)
  exact ⟨n, by omega, by omega, by omega, h3⟩

/-- Monotonicity of syndeticity. -/
theorem syndetic_mono {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (h : ∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧ P n) :
    ∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧ Q n := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, fun n₀ => by
    obtain ⟨n, h1, h2, h3⟩ := hL n₀
    exact ⟨n, h1, h2, hPQ n h3⟩⟩

/-! ### Upper Banach density -/

lemma ubd_ratio_le_one (A : Set ℤ) (M N : ℤ) :
    ((A ∩ Set.Ico M N).ncard : ℝ) / ((N : ℝ) - M) ≤ 1 := by
  rcases le_or_gt N M with h | h
  · have hle : ((N : ℝ) - M) ≤ 0 := by
      have : (N : ℝ) ≤ M := by exact_mod_cast h
      linarith
    exact (div_nonpos_of_nonneg_of_nonpos (by positivity) hle).trans zero_le_one
  · have hpos : (0 : ℝ) < (N : ℝ) - M := by
      have : (M : ℝ) < N := by exact_mod_cast h
      linarith
    rw [div_le_one hpos]
    have h1 : (A ∩ Set.Ico M N).ncard ≤ (Set.Ico M N).ncard :=
      Set.ncard_le_ncard Set.inter_subset_right (Set.finite_Ico M N)
    have h2 : ((Set.Ico M N).ncard : ℤ) = N - M := by
      rw [← Finset.coe_Ico, Set.ncard_coe_finset]; exact Int.card_Ico_of_le _ _ h.le
    have h3 : ((A ∩ Set.Ico M N).ncard : ℤ) ≤ N - M := by omega
    have h4 : (((A ∩ Set.Ico M N).ncard : ℤ) : ℝ) ≤ ((N - M : ℤ) : ℝ) := by exact_mod_cast h3
    push_cast at h4; exact h4

lemma ubd_ratio_nonneg (A : Set ℤ) (M N : ℤ) (h : M ≤ N) :
    0 ≤ ((A ∩ Set.Ico M N).ncard : ℝ) / ((N : ℝ) - M) := by
  apply div_nonneg (by positivity)
  have : (M : ℝ) ≤ N := by exact_mod_cast h
  linarith

lemma ubd_inner_le_one (A : Set ℤ) (L : ℕ) :
    (⨆ (M : ℤ) (N : ℤ) (_ : M + L ≤ N), ((A ∩ Set.Ico M N).ncard : ℝ) / ((N : ℝ) - M)) ≤ 1 :=
  Real.iSup_le (fun M => Real.iSup_le (fun N => Real.iSup_le (fun _ => ubd_ratio_le_one A M N)
    zero_le_one) zero_le_one) zero_le_one

lemma ubd_inner_nonneg (A : Set ℤ) (L : ℕ) :
    0 ≤ (⨆ (M : ℤ) (N : ℤ) (_ : M + L ≤ N), ((A ∩ Set.Ico M N).ncard : ℝ) / ((N : ℝ) - M)) :=
  Real.iSup_nonneg (fun M => Real.iSup_nonneg (fun N => Real.iSup_nonneg (fun h =>
    ubd_ratio_nonneg A M N (by omega))))

lemma ubd_ratio_le_inner (A : Set ℤ) (L : ℕ) (M N : ℤ) (h : M + L ≤ N) :
    ((A ∩ Set.Ico M N).ncard : ℝ) / ((N : ℝ) - M) ≤
      ⨆ (M : ℤ) (N : ℤ) (_ : M + L ≤ N), ((A ∩ Set.Ico M N).ncard : ℝ) / ((N : ℝ) - M) := by
  have bddN : ∀ M : ℤ, BddAbove (Set.range fun N : ℤ =>
      ⨆ (_ : M + L ≤ N), ((A ∩ Set.Ico M N).ncard : ℝ) / ((N : ℝ) - M)) := by
    intro M; refine ⟨1, ?_⟩; rintro _ ⟨N, rfl⟩
    exact Real.iSup_le (fun _ => ubd_ratio_le_one _ M N) zero_le_one
  have bddM : BddAbove (Set.range fun M : ℤ => ⨆ (N : ℤ) (_ : M + L ≤ N),
      ((A ∩ Set.Ico M N).ncard : ℝ) / ((N : ℝ) - M)) := by
    refine ⟨1, ?_⟩; rintro _ ⟨M, rfl⟩
    exact Real.iSup_le (fun N => Real.iSup_le (fun _ => ubd_ratio_le_one _ M N) zero_le_one)
      zero_le_one
  refine le_ciSup_of_le bddM M (le_ciSup_of_le (bddN M) N ?_)
  rw [ciSup_pos h]

theorem upperBanachDensity_le_one (A : Set ℤ) : upperBanachDensity A ≤ 1 :=
  (ciInf_le ⟨0, by rintro _ ⟨L, rfl⟩; exact ubd_inner_nonneg A L⟩ 0).trans (ubd_inner_le_one A 0)

theorem upperBanachDensity_nonneg (A : Set ℤ) : 0 ≤ upperBanachDensity A :=
  le_ciInf (fun L => ubd_inner_nonneg A L)

theorem upperBanachDensity_mono {A B : Set ℤ} (hAB : A ⊆ B) :
    upperBanachDensity A ≤ upperBanachDensity B := by
  refine le_ciInf fun L => ?_
  refine (ciInf_le ⟨0, by rintro _ ⟨L, rfl⟩; exact ubd_inner_nonneg A L⟩ L).trans ?_
  refine Real.iSup_le (fun M => Real.iSup_le (fun N => Real.iSup_le (fun h => ?_) ?_) ?_) ?_
  · refine le_trans ?_ (ubd_ratio_le_inner B L M N h)
    have hle : M ≤ N := by omega
    have hn : (A ∩ Set.Ico M N).ncard ≤ (B ∩ Set.Ico M N).ncard :=
      Set.ncard_le_ncard (Set.inter_subset_inter_left _ hAB) ((Set.finite_Ico M N).subset
        Set.inter_subset_right)
    rcases hle.eq_or_lt with rfl | hlt
    · simp
    · have : (0 : ℝ) < (N : ℝ) - M := by
        have : (M : ℝ) < N := by exact_mod_cast hlt
        linarith
      gcongr
  all_goals exact ubd_inner_nonneg B L

/-- Characterization of positive upper Banach density. -/
theorem upperBanachDensity_pos_iff (A : Set ℤ) :
    0 < upperBanachDensity A ↔
      ∃ c : ℝ, 0 < c ∧ ∀ L : ℕ, ∃ M N : ℤ, M + L ≤ N ∧
        c * ((N : ℝ) - M) ≤ ((A ∩ Set.Ico M N).ncard : ℝ) := by
  constructor
  · intro hpos
    refine ⟨upperBanachDensity A / 2, by linarith, fun L => ?_⟩
    by_contra hcon
    push Not at hcon
    have hle : (⨆ (M : ℤ) (N : ℤ) (_ : M + L ≤ N),
        ((A ∩ Set.Ico M N).ncard : ℝ) / ((N : ℝ) - M)) ≤ upperBanachDensity A / 2 := by
      refine Real.iSup_le (fun M => Real.iSup_le (fun N => Real.iSup_le (fun h => ?_) ?_) ?_) ?_
      · have hle : (M : ℝ) ≤ N := by exact_mod_cast (by omega : M ≤ N)
        rcases hle.eq_or_lt with h0 | hlt
        · rw [← h0]; simp; linarith
        · rw [div_le_iff₀ (by linarith)]
          have := hcon M N h
          linarith
      all_goals linarith
    have hge : upperBanachDensity A ≤ (⨆ (M : ℤ) (N : ℤ) (_ : M + L ≤ N),
        ((A ∩ Set.Ico M N).ncard : ℝ) / ((N : ℝ) - M)) :=
      ciInf_le ⟨0, by rintro _ ⟨L, rfl⟩; exact ubd_inner_nonneg A L⟩ L
    linarith
  · rintro ⟨c, hc, h⟩
    have : c ≤ upperBanachDensity A := by
      refine le_ciInf fun L => ?_
      obtain ⟨M, N, hMN, hcard⟩ := h (L + 1)
      have hMN' : M + L ≤ N := by push_cast at hMN; omega
      have hpos : (0 : ℝ) < (N : ℝ) - M := by
        have : (M : ℝ) < N := by exact_mod_cast (by push_cast at hMN; omega : M < N)
        linarith
      refine le_trans ?_ (ubd_ratio_le_inner A L M N hMN')
      rw [le_div_iff₀ hpos]; exact hcard
    linarith

theorem upperBanachDensity_pos_nonempty {A : Set ℤ} (h : 0 < upperBanachDensity A) :
    A.Nonempty := by
  obtain ⟨c, hc, hL⟩ := (upperBanachDensity_pos_iff A).1 h
  obtain ⟨M, N, hMN, hcard⟩ := hL 1
  have hpos : (0 : ℝ) < (N : ℝ) - M := by
    have : (M : ℝ) < N := by exact_mod_cast (by push_cast at hMN; omega : M < N)
    linarith
  have h0 : 0 < (A ∩ Set.Ico M N).ncard := by
    have : (0 : ℝ) < ((A ∩ Set.Ico M N).ncard : ℝ) := lt_of_lt_of_le (by positivity) hcard
    exact_mod_cast this
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero h0.ne'
  exact ⟨x, hx.1⟩

end CantorSzemeredi.Proof

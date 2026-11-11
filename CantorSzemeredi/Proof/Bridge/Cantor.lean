module

public import Mathlib
public import CantorSzemeredi.Frozen.CantorSet
public import CantorSzemeredi.Frozen.CantorEnum

/-!
# Bridge lemmas for the Cantor set and its enumeration

Basic facts about `cantorSet`/`cantorEnum`, the digit formula
`cantorEnum b D n = ofDigits b ((digits |D| n).map d)` (paper Lemma `l:Diff(i)`), the block
identity (`l:Diff(ii)`) and self-similarity.
-/

@[expose] public section

namespace CantorSzemeredi.Proof

open CantorSzemeredi

/-- The increasing listing `d : ℕ → ℕ` of `D` (zero beyond `D.card`). -/
noncomputable def cantorDigit (D : Finset ℕ) (i : ℕ) : ℕ :=
  if h : i < D.card then D.orderEmbOfFin rfl ⟨i, h⟩ else 0

lemma cantorDigit_mem {D : Finset ℕ} {i : ℕ} (h : i < D.card) : cantorDigit D i ∈ D := by
  simp [cantorDigit, h]

lemma cantorDigit_strictMonoOn {D : Finset ℕ} {i j : ℕ} (hij : i < j) (hj : j < D.card) :
    cantorDigit D i < cantorDigit D j := by
  have hi : i < D.card := hij.trans hj
  simp only [cantorDigit, hi, hj, dif_pos]
  exact (D.orderEmbOfFin rfl).strictMono (by simpa using hij)

lemma exists_cantorDigit_eq {D : Finset ℕ} {e : ℕ} (he : e ∈ D) :
    ∃ i, i < D.card ∧ cantorDigit D i = e := by
  have : e ∈ Set.range (D.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact he
  obtain ⟨⟨i, hi⟩, rfl⟩ := this
  exact ⟨i, hi, by simp [cantorDigit, hi]⟩

lemma cantorDigit_zero {D : Finset ℕ} (hD2 : 2 ≤ D.card) (hD0 : 0 ∈ D) : cantorDigit D 0 = 0 := by
  obtain ⟨i, hi, hie⟩ := exists_cantorDigit_eq hD0
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact hie
  · have := cantorDigit_strictMonoOn hpos hi
    omega

lemma cantorDigit_lt {b : ℕ} {D : Finset ℕ} (hDb : D ⊆ Finset.range b) {i : ℕ}
    (h : i < D.card) : cantorDigit D i < b := by
  simpa using hDb (cantorDigit_mem h)

/-- Recursive form of the enumeration. -/
noncomputable def cantorFun (b : ℕ) (D : Finset ℕ) (n : ℕ) : ℕ :=
  Nat.ofDigits b ((Nat.digits D.card n).map (cantorDigit D))

lemma cantorFun_zero (b : ℕ) (D : Finset ℕ) : cantorFun b D 0 = 0 := by
  simp [cantorFun]

lemma cantorFun_rec {b : ℕ} {D : Finset ℕ} (hD2 : 2 ≤ D.card) (hD0 : 0 ∈ D) (n : ℕ) :
    cantorFun b D n = cantorDigit D (n % D.card) + b * cantorFun b D (n / D.card) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cantorFun_zero, cantorDigit_zero hD2 hD0]
  · unfold cantorFun
    rw [Nat.digits_def' (by omega) hn]
    simp [Nat.ofDigits_cons]

lemma cantorFun_lt_aux {b : ℕ} {D : Finset ℕ} (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hD0 : 0 ∈ D) :
    StrictMono (cantorFun b D) := by
  have key : ∀ m n, n < m → cantorFun b D n < cantorFun b D m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hnm
      have hδ : 0 < D.card := by omega
      have hrn := cantorFun_rec (b := b) hD2 hD0 n
      have hrm := cantorFun_rec (b := b) hD2 hD0 m
      have hn' : n % D.card < D.card := Nat.mod_lt _ hδ
      have hm' : m % D.card < D.card := Nat.mod_lt _ hδ
      rcases lt_trichotomy (n / D.card) (m / D.card) with h | h | h
      · have := ih (m / D.card) (Nat.div_lt_self (by omega) (by omega)) (n / D.card) h
        have h1 := cantorDigit_lt hDb hn'
        nlinarith
      · have hmod : n % D.card < m % D.card := by
          have e1 := Nat.div_add_mod n D.card
          have e2 := Nat.div_add_mod m D.card
          rw [h] at e1
          nlinarith
        have := cantorDigit_strictMonoOn hmod hm'
        rw [hrn, hrm, h]; omega
      · exfalso
        have := Nat.div_le_div_right (c := D.card) hnm.le
        omega
  exact fun n m h => key m n h

lemma mem_cantorSet_iff {b : ℕ} {D : Finset ℕ} (hD0 : 0 ∈ D) (x : ℕ) :
    x ∈ cantorSet b D ↔ ∃ e ∈ D, ∃ y ∈ cantorSet b D, x = e + b * y := by
  have h0 : (0 : ℕ) ∈ cantorSet b D := ⟨0, fun _ => 0, fun _ _ => hD0, by simp⟩
  constructor
  · rintro ⟨k, d, hd, rfl⟩
    refine ⟨d 0, hd 0 (Nat.zero_le _), ∑ j ∈ Finset.range k, d (j + 1) * b ^ j, ?_, ?_⟩
    · rcases k with _ | k
      · simpa using h0
      · exact ⟨k, fun j => d (j + 1), fun j hj => hd _ (by omega), by
          simp [Finset.sum_range_succ]⟩
    · rw [Finset.sum_range_succ' _ k, Finset.mul_sum]
      simp only [pow_zero, mul_one, pow_succ]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
  · rintro ⟨e, he, y, ⟨k, d, hd, rfl⟩, rfl⟩
    refine ⟨k + 1, fun j => if j = 0 then e else d (j - 1), fun j hj => ?_, ?_⟩
    · by_cases h : j = 0 <;> simp [h, he, hd _ (by omega : j - 1 ≤ k)]
    · rw [Finset.sum_range_succ' _ (k + 1), Finset.mul_sum]
      simp only [pow_succ, ite_true, Nat.succ_ne_zero, Nat.add_sub_cancel, pow_zero,
        mul_one]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by simp <;> ring

lemma range_cantorFun {b : ℕ} {D : Finset ℕ} (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hD0 : 0 ∈ D) (hb : 3 ≤ b) :
    Set.range (cantorFun b D) = cantorSet b D := by
  have hδ : 0 < D.card := by omega
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rw [cantorFun_rec hD2 hD0]
      refine (mem_cantorSet_iff hD0 _).2 ⟨_, cantorDigit_mem (Nat.mod_lt _ hδ), _, ?_, rfl⟩
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa [cantorFun_zero] using (mem_cantorSet_iff hD0 0).2
          ⟨0, hD0, 0, ⟨0, fun _ => 0, fun _ _ => hD0, by simp⟩, by simp⟩
      · exact ih _ (Nat.div_lt_self hn (by omega))
  · intro hx
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      obtain ⟨e, he, y, hy, rfl⟩ := (mem_cantorSet_iff hD0 x).1 hx
      obtain ⟨i, hi, rfl⟩ := exists_cantorDigit_eq he
      have hyx : y < cantorDigit D i + b * y ∨ y = 0 := by
        rcases Nat.eq_zero_or_pos y with h | h
        · exact Or.inr h
        · exact Or.inl (by nlinarith)
      have hlt : y < cantorDigit D i + b * y ∨ (y = 0) := hyx
      obtain ⟨m, hm⟩ : ∃ m, cantorFun b D m = y := by
        rcases hlt with h | h
        · exact ih y h hy
        · exact ⟨0, by rw [h, cantorFun_zero]⟩
      refine ⟨D.card * m + i, ?_⟩
      rw [cantorFun_rec hD2 hD0]
      have h1 : (D.card * m + i) % D.card = i := by
        rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hi
      have h2 : (D.card * m + i) / D.card = m := by
        rw [Nat.mul_add_div hδ, Nat.div_eq_of_lt hi, add_zero]
      rw [h1, h2, hm]

/-- The Cantor set is infinite. -/
theorem cantorSet_infinite (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hD2 : 2 ≤ D.card)
    (hD0 : 0 ∈ D) : (cantorSet b D).Infinite := by
  obtain ⟨d, hd, hd0⟩ : ∃ d ∈ D, d ≠ 0 := by
    by_contra h; push Not at h
    have hsub : D ⊆ {0} := fun x hx => by simp [h x hx]
    have := Finset.card_le_card hsub; simp at this; omega
  refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => d * b ^ j) ?_ ?_
  · intro i j hij
    exact Nat.pow_right_injective (le_trans (by norm_num) hb)
      (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) hij)
  · intro j
    refine ⟨j, fun i => if i = j then d else 0, fun i _ => by
      show (if i = j then d else 0) ∈ D; split_ifs <;> assumption, ?_⟩
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · intro h; simp at h

theorem cantorEnum_zero (b : ℕ) (D : Finset ℕ) (hD0 : 0 ∈ D) : cantorEnum b D 0 = 0 :=
  Nat.nth_zero_of_zero ⟨0, fun _ => 0, fun _ _ => hD0, by simp⟩

theorem cantorEnum_strictMono (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hD2 : 2 ≤ D.card)
    (hD0 : 0 ∈ D) : StrictMono (cantorEnum b D) :=
  Nat.nth_strictMono (cantorSet_infinite b D hb hD2 hD0)

theorem range_cantorEnum (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hD2 : 2 ≤ D.card)
    (hD0 : 0 ∈ D) : Set.range (cantorEnum b D) = cantorSet b D :=
  Nat.range_nth_of_infinite (cantorSet_infinite b D hb hD2 hD0)

theorem cantorEnum_pos (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hD2 : 2 ≤ D.card)
    (hD0 : 0 ∈ D) {n : ℕ} (hn : 1 ≤ n) : 0 < cantorEnum b D n := by
  have := cantorEnum_strictMono b D hb hD2 hD0 (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  rwa [cantorEnum_zero b D hD0] at this

open Classical in
/-- Digit formula (paper Lemma `l:Diff(i)`). -/
theorem cantorEnum_eq_ofDigits (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hD0 : 0 ∈ D) (n : ℕ) :
    cantorEnum b D n = Nat.ofDigits b ((Nat.digits D.card n).map (cantorDigit D)) := by
  have hmono := cantorFun_lt_aux hb hDb hD2 hD0
  have hrange := range_cantorFun hDb hD2 hD0 hb
  change cantorEnum b D n = cantorFun b D n
  have hcount : ∀ n, Nat.count (· ∈ cantorSet b D) (cantorFun b D n) = n := by
    intro n
    rw [Nat.count_eq_card_filter_range]
    have : (Finset.range (cantorFun b D n)).filter (· ∈ cantorSet b D) =
        (Finset.range n).image (cantorFun b D) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hx, hxs⟩
        rw [← hrange] at hxs
        obtain ⟨m, rfl⟩ := hxs
        exact ⟨m, hmono.lt_iff_lt.1 hx, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨hmono hm, hrange ▸ ⟨m, rfl⟩⟩
    rw [this, Finset.card_image_of_injective _ hmono.injective, Finset.card_range]
  have := Nat.nth_count (p := (· ∈ cantorSet b D)) (n := cantorFun b D n)
    (by rw [← hrange]; exact ⟨n, rfl⟩)
  rw [hcount n] at this
  exact this

/-- The recursion `k_{δ n + r} = d_r + b k_n`. -/
theorem cantorEnum_rec (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hD0 : 0 ∈ D) (n : ℕ) :
    cantorEnum b D n =
      cantorDigit D (n % D.card) + b * cantorEnum b D (n / D.card) := by
  have h : ∀ n, cantorEnum b D n = cantorFun b D n :=
    fun n => cantorEnum_eq_ofDigits b D hb hDb hD2 hD0 n
  rw [h, h, cantorFun_rec hD2 hD0]

/-- Block identity (paper Lemma `l:Diff(ii)`). -/
theorem cantorEnum_block (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hD0 : 0 ∈ D) (i n j : ℕ) (hj : j < D.card ^ i) :
    cantorEnum b D (D.card ^ i * n + j) = b ^ i * cantorEnum b D n + cantorEnum b D j := by
  have hδ : 0 < D.card := by omega
  induction i generalizing n j with
  | zero =>
    have : j = 0 := by simpa using hj
    subst this
    simp [cantorEnum_zero b D hD0]
  | succ i ih =>
    have hj' : j / D.card < D.card ^ i := by
      rw [Nat.div_lt_iff_lt_mul hδ]; rwa [← pow_succ]
    have e1 : (D.card ^ (i + 1) * n + j) % D.card = j % D.card := by
      rw [pow_succ, mul_comm (D.card ^ i), mul_assoc]
      exact Nat.mul_add_mod _ _ _
    have e2 : (D.card ^ (i + 1) * n + j) / D.card = D.card ^ i * n + j / D.card := by
      rw [pow_succ, mul_comm (D.card ^ i), mul_assoc, Nat.mul_add_div hδ]
    rw [cantorEnum_rec b D hb hDb hD2 hD0 (D.card ^ (i + 1) * n + j), e1, e2,
      ih n _ hj', cantorEnum_rec b D hb hDb hD2 hD0 j]
    ring

/-- Self-similarity: `b ^ i * k_n = k_{δ ^ i * n}`. -/
theorem pow_mul_cantorEnum (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hD0 : 0 ∈ D) (i n : ℕ) :
    b ^ i * cantorEnum b D n = cantorEnum b D (D.card ^ i * n) := by
  have := cantorEnum_block b D hb hDb hD2 hD0 i n 0 (by positivity)
  simpa [cantorEnum_zero b D hD0] using this.symm

end CantorSzemeredi.Proof

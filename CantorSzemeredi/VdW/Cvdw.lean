/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.VdW.Focus

/-!
# The minimal case of the Cantor van der Waerden theorem

Blueprint: `blueprint/src/chapter/vdw.tex`, `thm:cvdw-minimal`.  In a minimal topological dynamical
system, every non-empty open set contains a progression `y, T^r y, …, T^{(L-1)r} y` with the common
difference `r ∈ b^h Cantor \ {0}`.
-/

namespace CantorSzemeredi

open Set Finset Filter Topology

namespace CantorData

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] {T : X → X}

/-- **Theorem `thm:cvdw-minimal`.**  In a minimal system, for every progression length `L ≥ 1`, every
non-empty open set `U` and every digit level `h`, there are `y` and `r ∈ b^h Cantor \ {0}` with
`T^{i r} y ∈ U` for `0 ≤ i < L`. -/
theorem topological_vdW_minimal (C : CantorData) (hT : Continuous T) (hmin : IsMinimalSys T)
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ (U : Set X), IsOpen U → U.Nonempty → ∀ h : ℕ,
      ∃ y : X, ∃ r : ℕ, C.Dig h r ∧ r ≠ 0 ∧ ∀ i < L, T^[i * r] y ∈ U := by
  induction L, hL using Nat.le_induction with
  | base =>
    intro U hU hne h
    obtain ⟨y, hy⟩ := hne
    have hpos : 0 < C.enum 1 := by
      have := C.enum_strictMono (show (0 : ℕ) < 1 by norm_num)
      rwa [C.enum_zero] at this
    refine ⟨y, C.base ^ h * C.enum 1, ⟨C.enum 1, ⟨1, rfl⟩, rfl⟩, ?_, ?_⟩
    · exact (Nat.mul_pos (pow_pos (by have := C.three_le_base; omega) h) hpos).ne'
    · intro i hi
      have : i = 0 := by omega
      subst this
      simpa using hy
  | succ L hL ih =>
    intro U hU hne h
    obtain ⟨ns, hcov⟩ := IsMinimalSys.exists_finset_cover hT hmin hU hne
    obtain ⟨x, α, k, hF⟩ := color_focusing C hT (hmin.surjective hT) hU hne ns hcov L h
      (fun V hV hVne h' => ih V hV hVne h') ns.card
    -- two points with the same colour
    obtain ⟨j1, hj1, j2, hj2, hne12, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := range (ns.card + 1)) (t := ns)
        (f := α) (by simp) fun j hj => hF.2.1 j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    have key : ∃ j j' : ℕ, j < j' ∧ j' ≤ ns.card ∧ α j = α j' := by
      have h1 := Finset.mem_range.1 hj1
      have h2 := Finset.mem_range.1 hj2
      rcases lt_or_gt_of_ne hne12 with h12 | h12
      · exact ⟨j1, j2, h12, by omega, heq⟩
      · exact ⟨j2, j1, h12, by omega, heq.symm⟩
    obtain ⟨j, j', hjj', hj'J, hαeq⟩ := key
    obtain ⟨hD, hr0, hsec⟩ := hF.2.2 j j' hjj' hj'J
    refine ⟨T^[α j] (x j'), sigmaSum k j j', hD, hr0, ?_⟩
    have comm : ∀ n, T^[n] (T^[α j] (x j')) = T^[α j] (T^[n] (x j')) := fun n => by
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]
    intro i hi
    rw [comm]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simp only [zero_mul, Function.iterate_zero, id_eq]
      rw [hαeq]
      exact hF.1 j' hj'J
    · exact hsec i hipos (by omega)

/-- Restriction of a map to an invariant subset. -/
lemma coe_iterate_restrict {F : Set X} (hF : MapsTo T F F) (n : ℕ) (z : F) :
    ((fun w : F => (⟨T w, hF w.2⟩ : F))^[n] z : X) = T^[n] (z : X) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]

/-- **Theorem `thm:cvdw`, dynamical form.**  For a topological dynamical system `(X, T)` and an open
cover `(U_a)`, for every `L ≥ 1` and every digit level `h` some `U_a` contains a progression
`x, T^r x, …, T^{(L-1) r} x` with `r ∈ b^h Cantor \ {0}`. -/
theorem topological_vdW (C : CantorData) [Nonempty X] (hT : Continuous T) {ι : Type*}
    (U : ι → Set X) (hUo : ∀ a, IsOpen (U a)) (hcov : ∀ x : X, ∃ a, x ∈ U a)
    (L : ℕ) (hL : 1 ≤ L) (h : ℕ) :
    ∃ a : ι, ∃ x : X, ∃ r : ℕ, C.Dig h r ∧ r ≠ 0 ∧ ∀ i < L, T^[i * r] x ∈ U a := by
  -- a minimal non-empty closed invariant subset, by Zorn's lemma
  set S : Set (Set X) := {F | IsClosed F ∧ F.Nonempty ∧ MapsTo T F F} with hS
  have hXS : (univ : Set X) ∈ S := ⟨isClosed_univ, univ_nonempty, fun x _ => mem_univ _⟩
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s := by
    intro c hcS hc hcne
    have hcdir : DirectedOn (· ⊇ ·) c := by
      intro A hA B hB
      rcases hc.total hA hB with h1 | h1
      · exact ⟨A, hA, subset_refl A, h1⟩
      · exact ⟨B, hB, h1, subset_refl B⟩
    haveI : Nonempty c := hcne.to_subtype
    have hne : (⋂₀ c).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed hcdir
        (fun F hF => (hcS hF).2.1) (fun F hF => (hcS hF).1.isCompact)
        (fun F hF => (hcS hF).1)
    refine ⟨⋂₀ c, ⟨?_, hne, ?_⟩, fun s hs => sInter_subset_of_mem hs⟩
    · exact isClosed_sInter fun F hF => (hcS hF).1
    · intro z hz
      exact fun F hF => (hcS hF).2.2 (hz F hF)
  obtain ⟨F, -, hFmin⟩ := zorn_superset_nonempty S hchain univ hXS
  obtain ⟨hFc, hFne, hFinv⟩ := hFmin.1
  -- the restriction of `T` to `F` is a minimal system
  let T' : F → F := fun w => ⟨T w, hFinv w.2⟩
  have hT' : Continuous T' := (hT.comp continuous_subtype_val).subtype_mk _
  haveI : CompactSpace F := isCompact_iff_compactSpace.1 hFc.isCompact
  have hmin' : IsMinimalSys T' := by
    intro G hGc hGne hGmaps
    have hG' : (Subtype.val '' G) ∈ S := by
      refine ⟨(hGc.isCompact.image continuous_subtype_val).isClosed, hGne.image _, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨T' z, hGmaps hz, rfl⟩
    have hsub : Subtype.val '' G ⊆ F := by
      rintro _ ⟨z, _, rfl⟩
      exact z.2
    have hF_sub := hFmin.2 hG' hsub
    apply Set.eq_univ_of_forall
    intro w
    obtain ⟨g, hg, hgw⟩ := hF_sub w.2
    have : g = w := Subtype.ext hgw
    exact this ▸ hg
  -- the cover of `F`
  obtain ⟨z0, hz0⟩ := hFne
  obtain ⟨a0, ha0⟩ := hcov z0
  have hne' : (Subtype.val ⁻¹' U a0 : Set F).Nonempty := ⟨⟨z0, hz0⟩, ha0⟩
  have hopen' : IsOpen (Subtype.val ⁻¹' U a0 : Set F) :=
    (hUo a0).preimage continuous_subtype_val
  obtain ⟨y, r, hD, hr0, hprog⟩ :=
    topological_vdW_minimal C hT' hmin' L hL _ hopen' hne' h
  refine ⟨a0, y.1, r, hD, hr0, fun i hi => ?_⟩
  have hy := hprog i hi
  have hiter : ((T'^[i * r] y : F) : X) = T^[i * r] (y : X) :=
    coe_iterate_restrict hFinv (i * r) y
  rw [← hiter]
  exact hy

end CantorData

end CantorSzemeredi

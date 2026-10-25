/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import Mathlib

/-!
# Minimal topological dynamical systems

Blueprint: `blueprint/src/chapter/vdw.tex`, `lem:minimal-facts`.  A topological dynamical system
`(X, T)` is *minimal* if its only non-empty closed invariant set is `X`.  For a minimal system on a
compact space, `T` is onto, every orbit meets every non-empty open set, and finitely many iterates
cover `X` by the preimages of a given non-empty open set.
-/

namespace CantorSzemeredi

open Set Filter Topology

/-- A topological dynamical system is minimal if every non-empty closed set `F` with `T(F) ⊆ F` is
the whole space. -/
def IsMinimalSys {X : Type*} [TopologicalSpace X] (T : X → X) : Prop :=
  ∀ F : Set X, IsClosed F → F.Nonempty → MapsTo T F F → F = univ

section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] {T : X → X}

/-- **Lemma `lem:minimal-facts` (a).**  For a minimal system, `T` is onto. -/
theorem IsMinimalSys.surjective (hT : Continuous T) (hmin : IsMinimalSys T) :
    Function.Surjective T := by
  intro y
  have hclosed : IsClosed (range T) := (isCompact_range hT).isClosed
  have hne : (range T).Nonempty := ⟨T y, y, rfl⟩
  have hinv : MapsTo T (range T) (range T) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨T z, rfl⟩
  have h := hmin (range T) hclosed hne hinv
  have hy : y ∈ range T := by
    rw [h]
    exact mem_univ y
  exact hy

/-- **Lemma `lem:minimal-facts` (b).**  In a minimal system every orbit meets every non-empty open
set. -/
theorem IsMinimalSys.exists_iterate_mem (hT : Continuous T) (hmin : IsMinimalSys T) (x : X)
    {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) : ∃ n : ℕ, T^[n] x ∈ U := by
  set O : Set X := range (fun n : ℕ => T^[n] x) with hO
  have hclosed : IsClosed (closure O) := isClosed_closure
  have hOne : (closure O).Nonempty := ⟨x, subset_closure ⟨0, rfl⟩⟩
  have hinv : MapsTo T (closure O) (closure O) := by
    intro z hz
    have h1 : T '' O ⊆ O := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n + 1, Function.iterate_succ_apply' T n x⟩
    have h2 : T '' closure O ⊆ closure (T '' O) := image_closure_subset_closure_image hT
    exact closure_mono h1 (h2 ⟨z, hz, rfl⟩)
  have hfull := hmin (closure O) hclosed hOne hinv
  obtain ⟨y, hy⟩ := hne
  have hyO : y ∈ closure O := by
    rw [hfull]
    exact mem_univ y
  obtain ⟨z, hzU, n, hzn⟩ := mem_closure_iff.1 hyO U hU hy
  exact ⟨n, by rw [show T^[n] x = z from hzn]; exact hzU⟩

/-- **Lemma `lem:minimal-facts` (c).**  In a minimal system, finitely many iterates cover `X` by
the preimages of a non-empty open set. -/
theorem IsMinimalSys.exists_finset_cover (hT : Continuous T) (hmin : IsMinimalSys T) {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ns : Finset ℕ, ∀ x : X, ∃ n ∈ ns, T^[n] x ∈ U := by
  have hopen : ∀ n : ℕ, IsOpen (T^[n] ⁻¹' U) := fun n => (hT.iterate n).isOpen_preimage U hU
  have hcover : univ ⊆ ⋃ n : ℕ, T^[n] ⁻¹' U := by
    intro x _
    obtain ⟨n, hn⟩ := hmin.exists_iterate_mem hT x hU hne
    exact mem_iUnion.2 ⟨n, hn⟩
  obtain ⟨ns, hns⟩ := isCompact_univ.elim_finite_subcover (fun n : ℕ => T^[n] ⁻¹' U) hopen hcover
  refine ⟨ns, fun x => ?_⟩
  have hx := hns (mem_univ x)
  obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.1 hx
  exact ⟨n, hn, hxn⟩

end

end CantorSzemeredi

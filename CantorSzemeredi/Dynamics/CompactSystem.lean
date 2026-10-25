/-
Copyright (c) 2026 Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena,
Maria Carmen Reguera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena, Maria Carmen Reguera
-/
import CantorSzemeredi.Dynamics.Localize
import CantorSzemeredi.Dynamics.CompactExtensionCSZ
import CantorSzemeredi.Dynamics.CSZ

/-!
# Compact systems are compact extensions of the trivial factor

Blueprint: `blueprint/src/chapter/csz.tex`, `lem:compact-system-extension`.

Over the trivial factor the conditional norm is the `L²` norm, so conditional compactness of an
orbit is ordinary total boundedness in `L²`.  The top factor `𝒜` is the whole σ-algebra.
-/

namespace CantorSzemeredi

open MeasureTheory Filter Topology

namespace MPS

variable {S : MPS}

/-- The top factor: the whole σ-algebra of the system. -/
def Factor.top (S : MPS) : Factor S where
  σ := S.measurableSpace
  le := le_rfl
  invariant s := by
    have hpre : S.measurableEquiv ⁻¹' s = S.T ⁻¹' s := by
      rw [← S.coe_measurableEquiv]
    rw [← hpre]
    exact S.measurableEquiv.measurableSet_preimage

/-- Over the trivial factor, the conditional norm is the `L²` norm, at every point. -/
theorem condNorm_trivial {u : S.X → ℝ} (hu : MemLp u 2 S.m) (x : S.X) :
    condNorm (Factor.trivial S) u x = (eLpNorm u 2 S.m).toReal := by
  have hsq := integral_sq_eq_eLpNorm_sq hu
  change Real.sqrt (S.m[u * u | (⊥ : MeasurableSpace S.X)] x) = _
  rw [condExp_bot]
  have h1 : ∫ y, (u * u) y ∂S.m = (eLpNorm u 2 S.m).toReal ^ 2 := by
    rw [← hsq]
    congr 1
    funext y
    simp [sq]
  change Real.sqrt (∫ y, (u * u) y ∂S.m) = _
  rw [h1, Real.sqrt_sq ENNReal.toReal_nonneg]

/-- **Lemma `lem:compact-system-extension`, the orbit step.**  If `f ∈ L²` is compact in the sense
of `CompactFunction`, then `f` is conditionally compact over the trivial factor, as an element of
`L²` of the top factor. -/
theorem condCompact_trivial_of_compactFunction {f : S.X → ℝ} (hf : MemLp f 2 S.m)
    (hcf : S.CompactFunction f) :
    CondCompact (Factor.trivial S) (Factor.top S) f := by
  intro ε hε
  have hm : ∀ m : ℤ, MemLp (f ∘ S.iter m) 2 S.m := fun m =>
    hf.comp_measurePreserving (S.measurePreserving_iter m)
  have hcf3 := hcf (ε / 3) (by positivity)
  obtain ⟨r, g, hgp, hcov⟩ := hcf3
  classical
  -- Each approximant is an orbit point of `f` close to the corresponding `g q`, if one exists.
  let h : Fin r → S.X → ℝ := fun q =>
    if hq : ∃ m : ℤ, eLpNorm (f ∘ S.iter m - g q) 2 S.m ≤ ENNReal.ofReal (ε / 3)
    then f ∘ S.iter (Classical.choose hq) else f
  have hh : ∀ q, MemL2 (Factor.top S) (h q) := by
    intro q
    by_cases hq : ∃ m : ℤ, eLpNorm (f ∘ S.iter m - g q) 2 S.m ≤ ENNReal.ofReal (ε / 3)
    · have hdef : h q = f ∘ S.iter (Classical.choose hq) := dif_pos hq
      rw [hdef]
      exact ⟨(hm _).aestronglyMeasurable, hm _⟩
    · have hdef : h q = f := dif_neg hq
      rw [hdef]
      exact ⟨hf.aestronglyMeasurable, hf⟩
  refine ⟨r, h, hh, fun n => Filter.Eventually.of_forall fun x => ?_⟩
  obtain ⟨q, hq⟩ := hcov (n : ℤ)
  have hex : ∃ m : ℤ, eLpNorm (f ∘ S.iter m - g q) 2 S.m ≤ ENNReal.ofReal (ε / 3) := ⟨n, hq⟩
  have hspec := Classical.choose_spec hex
  have hhq : h q = f ∘ S.iter (Classical.choose hex) := dif_pos hex
  have hiter : S.iter (n : ℤ) = S.T^[n] := S.iter_natCast n
  have hU : MemLp (f ∘ S.iter (n : ℤ) - g q) 2 S.m :=
    (hm _).sub (hgp q).2
  have hV : MemLp (f ∘ S.iter (Classical.choose hex) - g q) 2 S.m :=
    (hm _).sub (hgp q).2
  -- The difference of the two orbit points is controlled by the two errors.
  have hdiff : eLpNorm (f ∘ S.iter (n : ℤ) - h q) 2 S.m ≤ ENNReal.ofReal (2 * ε / 3) := by
    rw [hhq]
    have hfun : f ∘ S.iter (n : ℤ) - f ∘ S.iter (Classical.choose hex)
        = (f ∘ S.iter (n : ℤ) - g q) + -(f ∘ S.iter (Classical.choose hex) - g q) := by
      funext y
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
      ring
    have hfun' : f ∘ S.iter (n : ℤ) - f ∘ S.iter (Classical.choose hex)
        = f ∘ S.iter (n : ℤ) - f ∘ S.iter (Classical.choose hex) := rfl
    rw [hfun]
    refine le_trans (eLpNorm_add_le (by norm_num)) ?_
    rw [eLpNorm_neg]
    calc eLpNorm (f ∘ S.iter (n : ℤ) - g q) 2 S.m
          + eLpNorm (f ∘ S.iter (Classical.choose hex) - g q) 2 S.m
        ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := add_le_add hq hspec
      _ = ENNReal.ofReal (2 * ε / 3) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  have hfin : (eLpNorm (f ∘ S.iter (n : ℤ) - h q) 2 S.m).toReal < ε := by
    have hle := ENNReal.toReal_le_of_le_ofReal (by positivity) hdiff
    linarith
  refine ⟨q, ?_⟩
  have hMem : MemLp (f ∘ S.T^[n] - h q) 2 S.m := by
    rw [← hiter]
    exact (hm _).sub (hh q).memLp
  have hT : (f ∘ S.T^[n] - h q) = f ∘ S.iter (n : ℤ) - h q := by rw [hiter]
  rw [condNorm_trivial hMem, hT]
  exact hfin

/-- **Lemma `lem:compact-system-extension`.**  If the system is compact, then the top factor is a
compact extension of the trivial factor: every `f ∈ L²` is itself conditionally compact over the
trivial factor. -/
theorem compactExtension_of_compactSystem (hcs : S.CompactSystem) :
    CompactExtension (Factor.trivial S) (Factor.top S) := by
  intro f _ hmem ε hε
  refine ⟨f, condCompact_trivial_of_compactFunction hmem (hcs f hmem), ?_⟩
  simp

/-- **Corollary `cor:wm-compact-are-csz`, the compact part.**  A compact system is CSZ: it is a
compact extension of the trivial factor, which is CSZ. -/
theorem CSZ_of_compactSystem (hcs : S.CompactSystem) : (Factor.top S).CSZ :=
  csz_sets_of_compactExtension (Factor.trivial S) (Factor.top S) (Factor.trivial_CSZ S)
    (compactExtension_of_compactSystem hcs)

end MPS

end CantorSzemeredi

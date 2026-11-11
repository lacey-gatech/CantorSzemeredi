module

public import CantorSzemeredi.Port.Dynamics.CondHS
public import CantorSzemeredi.Port.Dynamics.Joining
public import Mathlib

/-!
# Dichotomy: shared definitions and the shift lemma

Definitions used by the later files of the dichotomy proof:

* `CondCompactZ D f` : conditional compactness over `ℤ` with approximants in `L²`
  (Moreira's min-inside form);
* `CondCompactZIn D E f` : the same with approximants in `L²(E)`, bridged to the ported
  `CSZPort.MPS.CondCompact` by `CondCompactZIn.condCompact`;
* `FibreTB D f x` : the `ℤ`-orbit of `f` is totally bounded in the fibre norm at `x`;
* `compactClass D` : the class 𝔄 of bounded measurable conditionally compact functions;
* `fibreNorm_shift` : `fibreNorm D g (T x) = fibreNorm D (g ∘ T) x` almost everywhere.
-/

@[expose] public section

namespace CantorSzemeredi.Proof

open MeasureTheory CSZPort CSZPort.MPS

variable {S : MPS} [StandardBorelSpace S.X]

/-- **Conditional compactness over `ℤ`** (Prelim.tex L166-179).

For every `ε > 0` there are finitely many `g q ∈ L²(m)` such that for every `n : ℤ`, for almost
every `x`, some `q` has `‖Tⁿ f - g q‖_{fibre x} < ε`.  This is Moreira's *min-inside* form (the
index `q` sits inside the a.e. quantifier and may depend on `x`), as in the paper's proof of
Theorem `t:compactExtension` (display `e:net`); the display in the paper's definition places the
minimum outside the `L^∞(D)` norm (see `docs/ERRATA-AND-DEVIATIONS.md`).  It differs from the
ported `CondCompact` by using orbits over `ℤ` and the fibre norm `fibreNorm`. -/
def CondCompactZ (D : Factor S) (f : S.X → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (r : ℕ) (g : Fin r → S.X → ℝ), (∀ q, MemLp (g q) 2 S.m) ∧
    ∀ n : ℤ, ∀ᵐ x ∂S.m, ∃ q : Fin r, fibreNorm D (f ∘ S.iter n - g q) x < ε

/-- `CondCompactZ` with the approximants required to lie in `L²(E)` (`MemL2 E`), for the bridge
to the ported `CondCompact D E`. -/
def CondCompactZIn (D E : Factor S) (f : S.X → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (r : ℕ) (g : Fin r → S.X → ℝ), (∀ q, MemL2 E (g q)) ∧
    ∀ n : ℤ, ∀ᵐ x ∂S.m, ∃ q : Fin r, fibreNorm D (f ∘ S.iter n - g q) x < ε

/-- **Fibrewise total boundedness**: at the point `x` the `ℤ`-orbit of
`f` has a finite `ε`-net, inside the orbit itself, for the fibre norm of `D` at `x`. -/
def FibreTB (D : Factor S) (f : S.X → ℝ) (x : S.X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ S' : Finset ℤ, ∀ n : ℤ, ∃ s ∈ S',
    fibreNorm D (f ∘ S.iter n - f ∘ S.iter s) x < ε

/-- **The class 𝔄**: bounded measurable functions that are
conditionally compact in the sense of `CondCompactZ`. -/
def compactClass (D : Factor S) : Set (S.X → ℝ) :=
  {f | Measurable f ∧ (∃ C : ℝ, ∀ x, |f x| ≤ C) ∧ CondCompactZ D f}

theorem CondCompactZIn.condCompactZ {D E : Factor S} {f : S.X → ℝ}
    (h : CondCompactZIn D E f) : CondCompactZ D f := fun ε hε => by
  obtain ⟨r, g, hg, h'⟩ := h ε hε
  exact ⟨r, g, fun q => (hg q).memLp, h'⟩

theorem mem_compactClass_iff {D : Factor S} {f : S.X → ℝ} :
    f ∈ compactClass D ↔
      Measurable f ∧ (∃ C : ℝ, ∀ x, |f x| ≤ C) ∧ CondCompactZ D f := Iff.rfl

omit [StandardBorelSpace S.X] in
/-- Bounded measurable functions are in `L²` of a probability space. -/
theorem memLp_two_of_bounded {f : S.X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : MemLp f 2 S.m :=
  MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hC x)

theorem compactClass_memLp {D : Factor S} {f : S.X → ℝ} (hf : f ∈ compactClass D) :
    MemLp f 2 S.m :=
  memLp_two_of_bounded hf.1 hf.2.1.choose_spec

/-- **Shift lemma.** For fixed `g ∈ L²`, `‖g‖_{fibre (T x)} = ‖g ∘ T‖_{fibre x}` for almost
every `x` (from `Factor.condExp_comp` applied to `g²`). -/
theorem fibreNorm_shift (D : Factor S) {g : S.X → ℝ} (hg : MemLp g 2 S.m) :
    ∀ᵐ x ∂S.m, fibreNorm D g (S.T x) = fibreNorm D (g ∘ S.T) x := by
  have hint : Integrable (fun y => g y ^ 2) S.m := hg.integrable_sq
  have hTm : MeasurePreserving S.T S.m S.m := S.measurePreserving
  have hint' : Integrable ((fun y => g y ^ 2) ∘ S.T) S.m :=
    (hTm.integrable_comp hint.aestronglyMeasurable).2 hint
  have h1 := condExp_eq_integral_condKernel D hint
  have h1' := hTm.quasiMeasurePreserving.ae h1
  have h2 := condExp_eq_integral_condKernel D hint'
  have h3 := Factor.condExp_comp D hint
  filter_upwards [h1', h2, h3] with x a b c
  simp only [fibreNorm, Function.comp] at a b c ⊢
  rw [← a, ← b, c]

/-- **Bridge to the ported notion.**  `CondCompactZIn D E f` (orbit over `ℤ`, fibre norm) gives
the ported `CondCompact D E f` (orbit over `ℕ`, `condNorm`), for `f ∈ L²`. -/
theorem CondCompactZIn.condCompact {D E : Factor S} {f : S.X → ℝ}
    (hf : MemLp f 2 S.m) (h : CondCompactZIn D E f) : CondCompact D E f := by
  intro ε hε
  obtain ⟨r, g, hg, h'⟩ := h ε hε
  refine ⟨r, g, hg, fun n => ?_⟩
  have hfn : MemLp (f ∘ S.T^[n]) 2 S.m :=
    hf.comp_measurePreserving (S.measurePreserving_T_iterate n)
  have hall : ∀ᵐ x ∂S.m, ∀ q : Fin r,
      condNorm D (f ∘ S.T^[n] - g q) x = fibreNorm D (f ∘ S.T^[n] - g q) x :=
    ae_all_iff.2 fun q => by
      have := ((hfn.sub (hg q).memLp).integrable_sq)
      refine condNorm_ae_eq_fibreNorm D ?_
      simpa [Pi.mul_def, sq] using this
  filter_upwards [hall, h' (n : ℤ)] with x hx hq
  obtain ⟨q, hq⟩ := hq
  exact ⟨q, by rw [hx q]; exact hq⟩

/-- ported bridge for `compactClass`-type data: `CondCompactZ` yields the ported notion when the
approximants already lie in `L²(E)`; this is `CondCompactZIn.condCompact`. -/
theorem condCompact_of_condCompactZIn {D E : Factor S} {f : S.X → ℝ}
    (hf : MemLp f 2 S.m) (h : CondCompactZIn D E f) : CondCompact D E f :=
  h.condCompact hf

end CantorSzemeredi.Proof

module

public import CantorSzemeredi.Frozen.CantorEnum
public import CantorSzemeredi.Proof.Assembly
public import CantorSzemeredi.Proof.Dichotomy.Main

/-!
# Provider for `CantorSzemeredi.cantor_szemeredi_syndetic` (Corollary `c:syndetic`)

Proves the frozen statement of `CantorSzemeredi/Frozen/Syndetic.lean`, copied verbatim except that the data binders are implicit and the hypotheses
are `:= by assumption` auto-parameters (so the frozen anchor's bare `by exact` applies), from
`cantor_szemeredi_syndetic_of_dichotomy` (`Proof/Assembly.lean`) and the dichotomy `dichotomy`
(`Proof/Dichotomy/Main.lean`). The frozen anchor's proof is `by exact CantorSzemeredi.Proof.cantor_szemeredi_syndetic`.
-/

@[expose] public section

open MeasureTheory

namespace CantorSzemeredi.Proof

/-- Provider for the frozen `CantorSzemeredi.cantor_szemeredi_syndetic` (Corollary `c:syndetic`). -/
theorem cantor_szemeredi_syndetic
    {b : ℕ} {D : Finset ℕ} (hb : 3 ≤ b := by assumption) (hDb : D ⊆ Finset.range b := by assumption)
    (hD2 : 2 ≤ D.card := by assumption) (hDb' : D.card < b := by assumption) (hD0 : 0 ∈ D := by assumption)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ := by assumption)
    {X : Type*} [MeasurableSpace X] {m : Measure X} [IsProbabilityMeasure m]
    {T : X ≃ᵐ X} (hT : MeasurePreserving T m m := by assumption)
    {f : X → ℝ} (hf : MemLp f ⊤ m := by assumption) (hf0 : 0 ≤ᵐ[m] f := by assumption) (hfne : ¬ f =ᵐ[m] 0 := by assumption) :
    ∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧
      0 < ∫ x, ∏ j ∈ Finset.range (ℓ + 1), f ((⇑T)^[j * cantorEnum b D n] x) ∂m :=
  cantor_szemeredi_syndetic_of_dichotomy dichotomy b D hb hDb hD2 hDb' hD0 ℓ hℓ m T hT f hf hf0 hfne

end CantorSzemeredi.Proof

module

public import CantorSzemeredi.Frozen.CantorEnum
public import CantorSzemeredi.Frozen.UpperBanachDensity
public import CantorSzemeredi.Proof.Assembly
public import CantorSzemeredi.Proof.Dichotomy.Main

/-!
# Provider for `CantorSzemeredi.cantor_szemeredi_integers` (Theorem `t:CSZ-Integers`)

Proves the frozen statement of `CantorSzemeredi/Frozen/Integers.lean`, copied verbatim except that the data binders are implicit and the hypotheses
are `:= by assumption` auto-parameters (so the frozen anchor's bare `by exact` applies), from
`cantor_szemeredi_integers_of_dichotomy` (`Proof/Assembly.lean`) and the dichotomy `dichotomy`
(`Proof/Dichotomy/Main.lean`). The frozen anchor's proof is `by exact CantorSzemeredi.Proof.cantor_szemeredi_integers`.
-/

@[expose] public section

open MeasureTheory

namespace CantorSzemeredi.Proof

/-- Provider for the frozen `CantorSzemeredi.cantor_szemeredi_integers` (Theorem `t:CSZ-Integers`). -/
theorem cantor_szemeredi_integers
    {b : ℕ} {D : Finset ℕ} (hb : 3 ≤ b := by assumption) (hDb : D ⊆ Finset.range b := by assumption)
    (hD2 : 2 ≤ D.card := by assumption) (hDb' : D.card < b := by assumption) (hD0 : 0 ∈ D := by assumption)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ := by assumption) {A : Set ℤ} (hA : 0 < upperBanachDensity A := by assumption) :
    (∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧ 1 ≤ n ∧
      0 < upperBanachDensity {a : ℤ | ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A}) ∧
    ∀ n : ℕ, 1 ≤ n →
      0 < upperBanachDensity {a : ℤ | ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A} →
      0 < cantorEnum b D n ∧ ∃ a : ℤ, ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A :=
  cantor_szemeredi_integers_of_dichotomy dichotomy b D hb hDb hD2 hDb' hD0 ℓ hℓ A hA

end CantorSzemeredi.Proof

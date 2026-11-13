import «section 4».EulerFiniteCuts
import Section3.GammaThresholdGeometry

/-! A bridge from actual first-order unary Gamma fibres to the constructed
Euler-function carrier. The finite-threshold theorem is checked in the
companion library from C-minimality, not supplied as an HK input. The result
here preserves the given base in its hypotheses. It does not yet identify
the definable closure of the finitely many thresholds it constructs. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section4.GammaDefinableEuler

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- The library's Gamma order is already the reversed valuation-norm order
(see `Values.vf_pred_iff_gamma_le`). Only the group notation is changed:
paper addition is library multiplication, and paper zero is library one. -/
abbrev PaperGamma := Additive (Values.Gamma (M := M))

def toPaperGamma : Values.Gamma (M := M) ≃ PaperGamma (M := M) := Additive.ofMul

theorem toPaperGamma_le (a b : Values.Gamma (M := M)) :
    toPaperGamma a ≤ toPaperGamma b ↔ a ≤ b := Iff.rfl

theorem toPaperGamma_mul (a b : Values.Gamma (M := M)) :
    toPaperGamma (a * b) = toPaperGamma a + toPaperGamma b := rfl

theorem toPaperGamma_one : toPaperGamma (1 : Values.Gamma (M := M)) = 0 := rfl

open EulerFunction

theorem definable_fibre_cut_control (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (f : PaperGamma (M := M) → ℤ) (m : ℤ)
    (hm : GammaParameters.GammaDefinableOverBase B {γ | f (toPaperGamma γ) = m}) :
    ∃ E : Finset (PaperGamma (M := M)), ∀ x y,
      (∀ c ∈ E, cutCode c x = cutCode c y) → (f x = m ↔ f y = m) := by
  obtain ⟨E, hE⟩ := GammaParameters.gamma_definable_finite_thresholds h00 B _ hm
  refine ⟨E.image toPaperGamma, ?_⟩
  intro x y hxy
  apply hE (toPaperGamma.symm x) (toPaperGamma.symm y)
  intro c hc
  have h := (cutCode_eq_iff (toPaperGamma c) x y).mp
    (hxy (toPaperGamma c) (Finset.mem_image.mpr ⟨c, hc, rfl⟩))
  exact h

theorem definable_function_finite_cuts (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (f : PaperGamma (M := M) → ℤ)
    (hf : (Set.range f).Finite)
    (hd : ∀ m : ℤ, GammaParameters.GammaDefinableOverBase B
      {γ | f (toPaperGamma γ) = m}) :
    ∃ n, ∃ a : Fin n → PaperGamma (M := M), CutDetermined a f :=
  exists_finite_cuts_of_finite_range f hf (fun m => definable_fibre_cut_control h00 B f m (hd m))

theorem exists_eulerFunction_of_definable (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (k : EulerKind)
    (f : PaperGamma (M := M) → ℤ) (hf : (Set.range f).Finite)
    (hd : ∀ m : ℤ, GammaParameters.GammaDefinableOverBase B
      {γ | f (toPaperGamma γ) = m}) :
    ∃ g : EulerFunction k (PaperGamma (M := M)), ∀ x, g x = f x := by
  obtain ⟨n, a, ha⟩ := definable_function_finite_cuts h00 B f hf hd
  exact exists_eulerFunction_of_finite_cuts k a f ha

end DiamondIntegral.Section4.GammaDefinableEuler

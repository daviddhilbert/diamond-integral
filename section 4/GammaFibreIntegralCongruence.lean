import «section 4».GammaWeightedFamilies

/-! Equality of actual unary fibres identifies their Euler integrals even
when their parameter presentations, arities or original bases differ. -/

set_option autoImplicit false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFibreIntegralCongruence
open GammaDefinableEuler GammaFamilyIntegration GammaWeightedFamilies EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem integralFirst_congr (h00 : M ⊨ Axioms.ACVF00) (B C : Base (M := M)) (k : EulerKind) {n m : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (g : (Fin (m + 1) → Values.Gamma (M := M)) → ℤ) (hg : IntegerFamilyDefinable C g)
    (y : Fin n → Values.Gamma (M := M)) (z : Fin m → Values.Gamma (M := M))
    (he : ∀ x : Values.Gamma (M := M), f (Fin.cons x y) = g (Fin.cons x z)) :
    integralFirst h00 B k f hf y = integralFirst h00 C k g hg z := by
  apply congrArg (totalEuler k)
  apply eval_injective k
  funext t
  obtain ⟨x, rfl⟩ := toPaperGamma.surjective t
  change fibreFunction h00 B k f hf y (toPaperGamma x) = fibreFunction h00 C k g hg z (toPaperGamma x)
  rw [fibreFunction_eval, fibreFunction_eval]
  exact he x

end DiamondIntegral.Section4.GammaFibreIntegralCongruence

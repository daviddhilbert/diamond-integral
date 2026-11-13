import «section 4».GammaOrdinaryRESEvaluation
import «section 4».GammaTranslationCharts

/-! Bare Gamma translations preserve both ordinary Euler evaluations.
The translation constants need only be Gamma-definable over the original
base. This numerical identity does not assert that an ordinary Gamma
morphism with an original-base RV lift exists. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryTranslations
open GammaOrdinaryCharts GammaOrdinaryRing
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def translatedChart (B : Base (M := M)) {n : ℕ} (a : Fin n → Values.Gamma (M := M))
    (ha : ∀ i, GammaDefinableClosureAtBase B (a i)) (c : Chart B n) : Chart B n :=
  ofSet B n (GammaTranslation.translated a c.support)
    (GammaTranslation.translated_definable B a ha c.support c.support_definable)

theorem ofWeighted_translated (B : Base (M := M)) {n : ℕ} (a : Fin n → Values.Gamma (M := M))
    (ha : ∀ i, GammaDefinableClosureAtBase B (a i)) (c : GammaWeightedCharts.Chart B n) :
    ofWeighted (GammaTranslationCharts.translatedChart B a ha c) = translatedChart B a ha (ofWeighted c) := rfl

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem evaluation_translated {R : Type*} [CommRing R] (t : R) (kind : EulerKind) {n : ℕ}
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (c : Chart B n) :
    GammaOrdinaryEulerEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ t kind
      (objectClass (translatedChart B a ha c)) =
    GammaOrdinaryEulerEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ t kind (objectClass c) := by
  rw [GammaOrdinaryEulerEvaluation.evaluation_class, GammaOrdinaryEulerEvaluation.evaluation_class]
  exact congrArg (fun z : ℤ => (z : R) * t ^ n)
    (GammaTranslation.integral_translated h00 linear hκ hs B hr hγ hΓ kind a ha c.support c.support_definable).symm

theorem resEvaluation_translated (kind : EulerKind) {n : ℕ}
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (c : Chart B n) :
    GammaOrdinaryRESEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ kind
      (objectClass (translatedChart B a ha c)) =
    GammaOrdinaryRESEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ kind (objectClass c) :=
  evaluation_translated h00 linear hκ hs B hr hγ hΓ (RESOrdinaryReduction.torusClass B) kind a ha c

end DiamondIntegral.Section4.GammaOrdinaryTranslations

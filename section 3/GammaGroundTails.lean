import «section 3».FullGammaFunctionOrder
import «section 3».GammaNativeTranslations
import «section 3».GammaGroundPointTranslations
import «section 3».GammaGroundGammaSemiringLift
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def gammaGroundGammaTail (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) :
    GammaGroundGammaPiece hc B 1 :=
  ⟨{γ | δ < γ 0},gammaGroundGammaPower_predicate_definable _
    ((FullGammaFunction.constant δ (integrationGammaDefinable hδ)).lt (FullGammaFunction.proj _ (0 : Fin 1)))⟩

def gammaGroundGammaPositiveTail : GammaGroundGammaPiece hc B 1 :=
  gammaGroundGammaTail 1 (gammaDefinableClosure_one B)

/-- The upper endpoint is included; the radius-zero annulus is empty. -/
def gammaGroundGammaAnnulus (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) :
    GammaGroundGammaPiece hc B 1 :=
  gammaGroundGammaPositiveTail.sdiff (gammaGroundGammaTail δ hδ)

theorem gammaGroundGammaAnnulus_mem (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) (γ : Fin 1 → Values.Gamma (M := M)) :
    γ ∈ (gammaGroundGammaAnnulus (hc := hc) δ hδ).carrier ↔ 1 < γ 0 ∧ γ 0 ≤ δ := by
  change (1 < γ 0 ∧ ¬ δ < γ 0) ↔ _
  exact and_congr Iff.rfl not_lt

/-- Translation of the full positive tail uses the stipulated old-ground
RV multiplier, not merely the existence of its Gamma value. -/
def gammaGroundGammaTailTranslation (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ)
    (c : Fin 1 → (CanonicalRV.RVSort M)ˣ)
    (hcdef : GammaGroundDefinable hc B (rawRVUnitSpace 1) {c})
    (hcval : rvUnitValueHom (c 0) = δ) :
    GammaGroundGammaObject.single (gammaGroundGammaPositiveTail (hc := hc) (B := B)) ⟶
      GammaGroundGammaObject.single (gammaGroundGammaTail δ hδ) := by
  apply gammaGroundGammaSinglePointTranslation _ _ c hcdef
  intro γ
  change (1 < γ 0) ↔ δ < rvUnitValueHom (c 0) * γ 0
  rw [hcval]
  have h : δ * 1 < δ * γ 0 ↔ 1 < γ 0 := mul_lt_mul_iff_left δ
  simpa only [mul_one] using h.symm
end DiamondIntegral.Section3

import «section 3».GammaNativeElementaryRelations
import «section 3».GammaNativeChainDensity

/-! The chain argument uses only fixed-degree scissors, actual measured
isomorphisms, and elementary relations. Exposing that additive universal
property supplies finite geometric witnesses before the principal quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {W : Type*} [AddCommMonoid W]

def gammaNativeAdditiveValue (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W)
    (U : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :=
  χ (gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization U ω))

def GammaNativeElementaryInvariant
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W) : Prop :=
  ∀ (U : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (i : Fin (n+1)) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i),
    gammaNativeAdditiveValue χ U ω = gammaNativeAdditiveValue χ (gammaElementaryAt hκ hs h00 hr U i hAd)
      (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd))

theorem gammaNativeAdditiveValue_hom (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W)
    (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (π : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaGroundMeasuredRVHom (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V π)) :
    gammaNativeAdditiveValue χ U ω = gammaNativeAdditiveValue χ V π :=
  congrArg χ (gammaGroundMeasuredRVClass_iso (asIso (show gammaNativeMeasuredNormalization U ω ⟶
    gammaNativeMeasuredNormalization V π from f)))

theorem gammaMeasuredClass_additive_scissor (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W)
    (X Y Z : GammaGroundMeasuredRVObject hc B (n+1))
    (h : gammaGroundMeasuredRVClass X + gammaGroundMeasuredRVClass Y = gammaGroundMeasuredRVClass Z) :
    χ (gammaGroundMeasuredRVClass X) + χ (gammaGroundMeasuredRVClass Y) = χ (gammaGroundMeasuredRVClass Z) :=
  (χ.map_add _ _).symm.trans (congrArg χ h)

end DiamondIntegral.Section3

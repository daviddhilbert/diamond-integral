import «section 3».GammaNativeElementaryHighDomain
import «section 3».GammaNativeElementaryDomain
import IntegrationSection6.FiniteGammaElementaryPartitions

/-! Restricting an elementary source to full structural weight leaves
exactly the same full-weight elementary labels and structural volumes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaNativeHigh_admissible (U : GammaObjectAt B Set.univ (n+1)) (i : Fin (n+1))
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    GammaAdmissible (gammaHighRestrictionAt U).toGamma.toGammaRVObject i where
  nonzero a := hAd.nonzero ⟨a.val,a.property.1⟩
  algebraic a := hAd.algebraic ⟨a.val,a.property.1⟩

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
variable (U : GammaObjectAt B Set.univ (n+1)) (i : Fin (n+1))
variable (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
local notation "EU" => gammaElementaryAt hκ hs h00 hr U i hAd
local notation "EH" => gammaElementaryAt hκ hs h00 hr (gammaHighRestrictionAt U) i (gammaNativeHigh_admissible U i hAd)

theorem gammaNativeElementary_high_domain_eq :
    (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt (EH))).carrier =
      (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt (EU))).carrier :=
  (gammaNativeElementary_positive_domain hκ hs h00 hr (gammaHighRestrictionAt U) (gammaHighRestriction_fullWeight U)
    i (gammaNativeHigh_admissible U i hAd)).trans
    (gammaNativeElementary_high_product_domain hκ hs h00 hr U i hAd).symm

def gammaNativeElementaryHighBijection : GammaGroundBijection
    (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt (EH)))
    (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt (EU))) :=
  GammaGroundBijection.ofCarrierEq (gammaNativeElementary_high_domain_eq hκ hs h00 hr U i hAd)

theorem gammaNativeElementaryHighBijection_volume
    (w : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt (EH))) :
    (Section5.nativeRVGroundVolume (gammaHighRestrictionAt (EU))
      ((gammaNativeElementaryHighBijection hκ hs h00 hr U i hAd).map w)).val =
      (Section5.nativeRVGroundVolume (gammaHighRestrictionAt (EH)) w).val := by
  let A := @complement M N Set.univ (n+1) U.object.obj (@rvLowDomain M N Set.univ n U.object.obj)
  let hA := @complement_subset M N hN Set.univ (n+1) U.object.obj (@rvLowDomain M N Set.univ n U.object.obj)
  let qH := Section5.nativeRVGroundDomainEquiv (gammaHighRestrictionAt (EH)) w
  let q : rvObjectDomain (EH).object.obj := ⟨qH.val,qH.property.1⟩
  let a := @elementarySubobjectMap M N hN Set.univ (n+1) U.object.obj i A hA q
  let qU := Section5.nativeRVGroundDomainEquiv (gammaHighRestrictionAt (EU))
    ((gammaNativeElementaryHighBijection hκ hs h00 hr U i hAd).map w)
  let b : rvObjectDomain (EU).object.obj := ⟨qU.val,qU.property.1⟩
  have he : a = b := Subtype.ext (@elementarySubobjectMap_labels M N hN Set.univ (n+1) U.object.obj i A hA q)
  rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
  change @SpecialTransformations.Section4.RVObject.value M N Set.univ (n+1) (EU).object.obj b =
    @SpecialTransformations.Section4.RVObject.value M N Set.univ (n+1) (EH).object.obj q
  rw [← he]
  exact @elementarySubobjectMap_volume M N hN Set.univ (n+1) U.object.obj i A hA q

end DiamondIntegral.Section3

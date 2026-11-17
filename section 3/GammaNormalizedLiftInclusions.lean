import «section 3».GammaNativeFullLiftDomain
import «section 3».GammaNativeMeasuredIsomorphisms

/-! Full-weight local lifts embed literally in their native lifts. A
native lift point lies in the full-weight lift whenever its retained
label belongs to that full-weight RV domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
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

 theorem gammaNormalizedLift_subset (U : GammaObjectAt B Set.univ (n+1)) :
    (gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt U)
      (gammaHighRestriction_fullWeight U))).carrier ⊆ (gammaNativeUnitLift (hc := hc) U.toGamma).domain.carrier := by
  intro p hp
  have hh := (gammaNativeFullLift_carrier (hc := hc) (gammaHighRestrictionAt U) (gammaHighRestriction_fullWeight U)).ge hp
  obtain ⟨u,hu,hv⟩ := hh
  exact ⟨⟨u.val,u.property.1⟩,hu,hv⟩

def gammaNormalizedLiftInclusion (U : GammaObjectAt B Set.univ (n+1)) :
    GammaGroundMap (gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt U)
      (gammaHighRestriction_fullWeight U))) (gammaNativeUnitLift (hc := hc) U.toGamma).domain :=
  GammaGroundMap.inclusion (gammaNormalizedLift_subset U)

theorem gammaNormalizedLiftInclusion_label (U : GammaObjectAt B Set.univ (n+1))
    (p : gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt U)
      (gammaHighRestriction_fullWeight U))) :
    gammaNativeLiftLabel U (gammaNormalizedLiftInclusion U p) = gammaNativeHighLabelInclusion U
      (gammaGroundObjectLiftLabel (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt U)
        (gammaHighRestriction_fullWeight U)) p) := by
  apply Subtype.ext
  rfl

theorem gammaNormalizedLift_of_label (U : GammaObjectAt B Set.univ (n+1))
    (p : (gammaNativeUnitLift (hc := hc) U.toGamma).domain)
    (w : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U))
    (hw : w.val = p.val.2) :
    p.val ∈ (gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt U)
      (gammaHighRestriction_fullWeight U))).carrier := by
  obtain ⟨u,hu,hv⟩ := p.property
  let wU := gammaNativeHighLabelInclusion U w
  let u' := Section5.nativeRVGroundDomainEquiv U wU
  have he : u = u' := Subtype.ext (hu.trans hw.symm)
  refine ⟨w,hw,?_⟩
  change (Section5.nativeRVGroundVolume (gammaHighRestrictionAt U) w).val = Section2.tupleRV M p.val.1
  rw [← gammaNativeHigh_groundVolume]
  exact (gammaNativeRVGroundVolume_value U wU).trans
    ((congrArg (fun z : rvObjectDomain U.object.obj => (rvObjectVolume U.object.obj z).val) he).symm.trans
      (hv.trans (Section5.completed18_tupleRV p.val.1)))

end DiamondIntegral.Section3

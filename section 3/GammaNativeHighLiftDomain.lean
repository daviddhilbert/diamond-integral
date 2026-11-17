import «section 3».GammaNativeStructuralValues
import «section 3».GammaMeasuredCofullRestriction
import «section 5».Completed18LocalLift

/-! Full structural weight is exactly the cofull nonzero VF stratum of a
native lift. This removes no top-dimensional VF points. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
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

theorem gammaNativeHighLift_carrier (U : GammaObjectAt B Set.univ (n+1)) :
    (Section5.nativeVFZeroStratum (gammaNativeUnitLift (hc := hc) U.toGamma).domain Finset.univ).carrier =
      (gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt U)
        (gammaHighRestriction_fullWeight U))).carrier := by
  let H := gammaHighRestrictionAt U
  let W := Section5.nativeRVGroundObject (hc := hc) H (gammaHighRestriction_fullWeight U)
  ext p
  rw [Section5.nativeVFZeroStratum_mem]
  constructor
  · rintro ⟨⟨u,hu,hv⟩,hn⟩
    have hvalue : (rvObjectVolume U.object.obj u).val = Section2.tupleRV M p.1 :=
      hv.trans (Section5.completed18_tupleRV p.1)
    have hNZ (j : Fin (n+1)) : ((rvObjectVolume U.object.obj u).val j).val ≠ @iRVZero M N := by
      intro hz
      have hz' : rvValues (Section2.tupleRV M p.1) j = @iRVZero M sM :=
        (congrArg (fun t : Fin (n+1) → CanonicalRV.RVSort M => (t j).val) hvalue).symm.trans
          (hz.trans (CanonicalStructure.sortZero_normalize .rv))
      exact ((hn j).mp (Finset.mem_univ _)) ((Section5.rvValues_tupleRV_zero_iff p.1 j).mp hz')
    let uH : rvObjectDomain H.object.obj := ⟨u.val,u.property,by
      intro hl
      obtain ⟨j,hj⟩ := (@rvWeight_le_pred_iff_zero M N n
        (rvObjectVolume U.object.obj u).val).mp
        ((@mem_rvLowDomain M N Set.univ n U.object.obj u).mp hl)
      exact hNZ j hj⟩
    let w : W.domain := (Section5.nativeRVGroundDomainEquiv H).symm uH
    refine ⟨w,hu,?_⟩
    have hw := gammaNativeRVGroundVolume_value H w
    change (Section5.nativeRVGroundVolume H w).val = _
    exact hw.trans hvalue
  · rintro ⟨w,hw,hv⟩
    let uH := Section5.nativeRVGroundDomainEquiv H w
    let u : rvObjectDomain U.object.obj := ⟨uH.val,uH.property.1⟩
    have hvalue : (rvObjectVolume U.object.obj u).val = Section2.tupleRV M p.1 :=
      (gammaNativeRVGroundVolume_value H w).symm.trans hv
    refine ⟨⟨u,hw,hvalue.trans (Section5.completed18_tupleRV p.1).symm⟩,?_⟩
    intro j
    refine ⟨fun _ hz => ?_,fun _ => Finset.mem_univ _⟩
    apply W.nonzero w j
    exact (congrArg (fun t : Fin (n+1) → CanonicalRV.RVSort M => (t j).val) hv).trans
      ((Section5.rvValues_tupleRV_zero_iff p.1 j).mpr hz)

end DiamondIntegral.Section3

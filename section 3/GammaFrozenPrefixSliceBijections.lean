import «section 3».GammaFrozenPrefixSliceMaps

/-! Full native slice maps are actual original-Gamma bijections. The
inverse is obtained from the full inverse map and fixes the same frozen
VF prefix. No quotient-class argument is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ}
variable (U V : GammaObjectAt B Set.univ (p+1))
variable (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
variable (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V)) (N L : ℕ)
variable (x : Fin p → VF (M := M))
variable (hF : (gammaNativeMeasuredVFSliceSchema U ω N).valid (vfValues x))
variable (hG : (gammaNativeMeasuredVFSliceSchema V η L).valid (vfValues x))
variable (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (rvObjectArity U.object.obj) 1
  ((gammaNativeMeasuredVFSliceSchema U ω N).object.rowDomain (vfValues x))
  ((gammaNativeMeasuredVFSliceSchema U ω N).object.rowVolume (vfValues x)))
variable (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (rvObjectArity V.object.obj) 1
  ((gammaNativeMeasuredVFSliceSchema V η L).object.rowDomain (vfValues x))
  ((gammaNativeMeasuredVFSliceSchema V η L).object.rowVolume (vfValues x)))
variable (f : GammaGroundBijection (gammaNativeUnitLift (hc := hc) U.toGamma).domain (gammaNativeUnitLift V.toGamma).domain)
variable (hFix : ∀ q, (f.map q).val.1 ∘ Fin.castAdd 1 = q.val.1 ∘ Fin.castAdd 1)


theorem gammaNativeUnarySliceMap_bijective :
    Function.Bijective (gammaNativeUnarySliceMap U V ω η N L x hF hG P Q f hFix) := by
  have hInv : ∀ v, (f.symm.map v).val.1 ∘ Fin.castAdd 1 = v.val.1 ∘ Fin.castAdd 1 := by
    intro v
    have h := hFix (f.symm.map v)
    have hi : f.map (f.symm.map v) = v := f.map.apply_inverse f.bijective v
    rw [hi] at h
    exact h.symm
  let g := gammaNativeUnarySliceMap V U η ω L N x hG hF Q P f.symm hInv
  constructor
  · intro q r h
    apply gammaNativeSliceRowOriginalPoint_injective U ω N x hF P
    apply f.bijective.1
    exact (gammaNativeUnarySliceMap_square U V ω η N L x hF hG P Q f hFix q).symm.trans
      ((congrArg (gammaNativeSliceRowOriginalPoint V η L x hG Q) h).trans
        (gammaNativeUnarySliceMap_square U V ω η N L x hF hG P Q f hFix r))
  · intro r
    refine ⟨g r,?_⟩
    apply gammaNativeSliceRowOriginalPoint_injective V η L x hG Q
    exact (gammaNativeUnarySliceMap_square U V ω η N L x hF hG P Q f hFix (g r)).trans
      ((congrArg f.map (gammaNativeUnarySliceMap_square V U η ω L N x hG hF Q P f.symm hInv r)).trans
        (f.map.apply_inverse f.bijective (gammaNativeSliceRowOriginalPoint V η L x hG Q r)))

def gammaNativeUnarySliceBijection :
    GammaGroundBijection (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain
      (gammaNativeUnitLift (hc := hc) (gammaUniversalObject Q.toGamma).toGamma).domain :=
  ⟨gammaNativeUnarySliceMap U V ω η N L x hF hG P Q f hFix,
    gammaNativeUnarySliceMap_bijective U V ω η N L x hF hG P Q f hFix⟩

end DiamondIntegral.Section3

import «section 3».GammaFrozenPrefixForms
import «section 5».NativeMixedCoordinateMaps

/-! A full original-Gamma bijection fixing a VF prefix induces the
actual map of native unary slice lifts. Its square with the original
full lift maps commutes on every point. -/
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

include hF hG hFix in
def gammaNativeUnarySliceMap :
    GammaGroundMap (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain
      (gammaNativeUnitLift (hc := hc) (gammaUniversalObject Q.toGamma).toGamma).domain := by
  let I := gammaNativeSliceRowInclusion U ω N x hF P
  let pre := (f.map.monoReal Set.subset_union_left).comp I
  let out := Section5.nativeMixedCoordinateMap
    ((gammaNativeUnitLift (hc := hc) V.toGamma).domain.monoReal (T := B.real ∪ Set.range (vfValues x)) Set.subset_union_left)
    (Fin.natAdd p : Fin 1 → Fin (p+1)) id
  apply (out.comp pre).corestrict
  intro q
  let u := gammaNativeSliceRowOriginalPoint U ω N x hF P q
  let v := f.map u
  have hPrefix : v.val.1 ∘ Fin.castAdd 1 = x :=
    (hFix u).trans (funext (Fin.append_left _ _))
  change (v.val.1 ∘ Fin.natAdd p,v.val.2) ∈ (gammaNativeUnitLift (hc := hc) (gammaUniversalObject Q.toGamma).toGamma).domain.carrier
  apply (gammaNativeSliceRow_lift V η L x hG Q _).mpr
  have hRestore : (Fin.append x (v.val.1 ∘ Fin.natAdd p),v.val.2) = v.val :=
    Prod.ext ((congrArg (fun z => Fin.append z (v.val.1 ∘ Fin.natAdd p)) hPrefix).symm.trans Fin.append_castAdd_natAdd) rfl
  exact hRestore.symm ▸ v.property

theorem gammaNativeUnarySliceMap_value
    (q : (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain) :
    (gammaNativeUnarySliceMap U V ω η N L x hF hG P Q f hFix q).val =
      ((f.map (gammaNativeSliceRowOriginalPoint U ω N x hF P q)).val.1 ∘ Fin.natAdd p,
        (f.map (gammaNativeSliceRowOriginalPoint U ω N x hF P q)).val.2) := rfl

theorem gammaNativeUnarySliceMap_square
    (q : (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain) :
    gammaNativeSliceRowOriginalPoint V η L x hG Q (gammaNativeUnarySliceMap U V ω η N L x hF hG P Q f hFix q) =
      f.map (gammaNativeSliceRowOriginalPoint U ω N x hF P q) := by
  let u := gammaNativeSliceRowOriginalPoint U ω N x hF P q
  let v := f.map u
  have hPrefix : v.val.1 ∘ Fin.castAdd 1 = x := (hFix u).trans (funext (Fin.append_left _ _))
  apply Subtype.ext
  change (Fin.append x (v.val.1 ∘ Fin.natAdd p),v.val.2) = v.val
  exact Prod.ext ((congrArg (fun z => Fin.append z (v.val.1 ∘ Fin.natAdd p)) hPrefix).symm.trans Fin.append_castAdd_natAdd) rfl

end DiamondIntegral.Section3

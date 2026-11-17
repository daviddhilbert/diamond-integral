import «section 3».GammaUnaryGeometryBaseReduction
import IntegrationSection6.GammaFieldBaseReduction

/-! The unary measured geometric proof works over an arbitrary original
real/Gamma base. The generated coefficient field is eliminated from the
actual complete proof, including its forms and algebraic centers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativeUnaryFullMeasured_original_base_geometry
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U V : GammaObjectAt B Set.univ 1)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η)) :
    GammaUnaryMeasuredGeometry hκ.le hs h00 hr
      (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V η) := by
  let C := vfFieldNamedBase B
  let hBC : B.real ⊆ C.real := Set.subset_union_left
  let hrC := vfFieldNamedBase_small B hκ hr
  let UC := gammaNativeRealBaseExtend U hBC
  let VC := gammaNativeRealBaseExtend V hBC
  let ωC := gammaNativeRealBaseExtendForm U ω hBC
  let ηC := gammaNativeRealBaseExtendForm V η hBC
  have fC : GammaFullMeasuredBijection (gammaNativeMeasuredLift UC ωC) (gammaNativeMeasuredLift VC ηC) := by
    rw [gammaNativeRealBaseExtend_lift,gammaNativeRealBaseExtend_lift]
    exact f.monoReal hBC
  have hC := gammaNativeUnaryFullMeasured_local_geometry hκ hs h00 hrC hv δ hδ hδ1
    (vfFieldNamedBase_field B) UC VC ωC ηC fC
  have hB := gammaUnaryMeasuredGeometry_reduce hκ.le hs h00 hrC hr (vfFieldBaseReduction B) hC
  have hU : gammaGroundMeasuredRVReduceObject (vfFieldBaseReduction B) (gammaNativeMeasuredNormalization UC ωC) =
      gammaNativeMeasuredNormalization U ω :=
    (congrArg (gammaGroundMeasuredRVReduceObject (vfFieldBaseReduction B))
      (gammaNativeMeasuredNormalization_monoReal U ω hBC)).trans
        (gammaGroundMeasuredRVReduce_monoReal hBC (vfFieldBaseReduction B) (gammaNativeMeasuredNormalization U ω))
  have hV : gammaGroundMeasuredRVReduceObject (vfFieldBaseReduction B) (gammaNativeMeasuredNormalization VC ηC) =
      gammaNativeMeasuredNormalization V η :=
    (congrArg (gammaGroundMeasuredRVReduceObject (vfFieldBaseReduction B))
      (gammaNativeMeasuredNormalization_monoReal V η hBC)).trans
        (gammaGroundMeasuredRVReduce_monoReal hBC (vfFieldBaseReduction B) (gammaNativeMeasuredNormalization V η))
  rw [hU,hV] at hB
  exact hB

end DiamondIntegral.Section3

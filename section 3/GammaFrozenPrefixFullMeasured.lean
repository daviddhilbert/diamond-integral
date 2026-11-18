import «section 3».GammaFrozenPrefixSliceBijections
import «section 3».GammaFrozenPrefixSliceJacobians
import «section 3».GammaFrozenPrefixIndependence
import «section 3».GammaFullMeasuredBijections

/-! A generic frozen prefix restricts an actual full measured native
bijection to an actual full measured unary slice bijection. Original
Gamma densities and the actual unary Jacobian are retained. -/
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
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
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
variable (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η))
variable (hFix : ∀ q, (f.map.map q).val.1 ∘ Fin.castAdd 1 = q.val.1 ∘ Fin.castAdd 1)


def gammaNativeUnarySliceFullMeasured
    (hx : AlgebraicIndependent (vfParameterField B.real) x) :
    GammaFullMeasuredBijection
      (gammaNativeMeasuredLift (gammaUniversalObject P.toGamma)
        ((gammaNativeMeasuredVFSliceSchema U ω N).rawRowForm (vfValues x) hF P))
      (gammaNativeMeasuredLift (gammaUniversalObject Q.toGamma)
        ((gammaNativeMeasuredVFSliceSchema V η L).rawRowForm (vfValues x) hG Q)) where
  map := gammaNativeUnarySliceBijection U V ω η N L x hF hG P Q f.map hFix
  measure := by
    intro q hq
    let u := gammaNativeSliceRowOriginalPoint U ω N x hF P q
    have hu : AlgebraicIndependent (vfParameterField B.real) u.val.1 := gammaFrozenPrefix_independent x q.val.1 hx hq
    obtain ⟨J,hJ,hw⟩ := f.measure u hu
    have hSlice := gammaNativeUnarySliceMap_jacobian U V ω η N L x hF hG P Q f.map hFix q J hJ
    refine ⟨J,hSlice,?_⟩
    rw [gammaNativeSliceRow_weight,gammaNativeSliceRow_weight]
    exact hw.trans (congrArg
      (fun v => gammaGroundMeasuredVFWeight (gammaNativeMeasuredLift V η) v * Values.vfValueHom J)
      (gammaNativeUnarySliceMap_square U V ω η N L x hF hG P Q f.map hFix q).symm)

end DiamondIntegral.Section3

import «section 3».GammaHeadRetainedForms
import «section 3».GammaUniformTraceFormTransport
import «section 5».NativeMixedCoordinateMaps

/-! The head canonical lift pulls the actual contracted Gamma form back
along the literal frozen-tail projection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
variable {U : DefSet (M := M) Set.univ (n+1) a}

def gammaHeadLiftDrop (T : HeadPreparation U) (hTarget : GammaSetDefinable B (carrier T.target)) :
    GammaGroundMap
      (Section5.nativeGammaPointDomain (hc := hc) (carrier T.liftSet) (gamma_coordinateCanonicalImage T.target hTarget 0))
      (Section5.nativeGammaPointDomain (carrier T.contractedSet) (gamma_headImage T.target hTarget)) :=
  (Section5.nativeMixedCoordinateMap
    (Section5.nativeGammaPointDomain (hc := hc) (carrier T.liftSet) (gamma_coordinateCanonicalImage T.target hTarget 0))
    Fin.succ id).corestrict (fun p => ((T.liftSet_exact p.val).mp p.property).1)

theorem gammaHeadLiftDrop_lift (T : HeadPreparation U) (hTarget : GammaSetDefinable B (carrier T.target)) (u : U) :
    gammaHeadLiftDrop (hc := hc) T hTarget ⟨(T.liftMap u).val,(T.liftMap u).property⟩ =
      ⟨(T.contractionMap u).val,(T.contractionMap u).property⟩ :=
  Subtype.ext (T.lifting_square u)

def gammaHeadLiftForm (T : HeadPreparation U) (hTarget : GammaSetDefinable B (carrier T.target))
    (Q : GammaGroundDefSet hc B (SpecialTransformations.Section4.rawRVSpace (M := M) a))
    (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    GammaGroundVolumeForm hc B
      (Section5.nativeGammaPointDomain (carrier T.liftSet) (gamma_coordinateCanonicalImage T.target hTarget 0)) :=
  (gammaHeadContractedForm T hTarget Q hLabels ω).comp (gammaHeadLiftDrop T hTarget)

theorem gammaHeadLiftForm_apply (T : HeadPreparation U) (hTarget : GammaSetDefinable B (carrier T.target))
    (Q : GammaGroundDefSet hc B (SpecialTransformations.Section4.rawRVSpace (M := M) a))
    (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) (u : U) :
    gammaHeadLiftForm T hTarget Q hLabels ω ⟨(T.liftMap u).val,(T.liftMap u).property⟩ = ω ⟨u.val.2,hLabels u⟩ := by
  change gammaHeadContractedForm T hTarget Q hLabels ω (gammaHeadLiftDrop T hTarget ⟨(T.liftMap u).val,(T.liftMap u).property⟩) = _
  rw [gammaHeadLiftDrop_lift]
  exact gammaHeadContractedForm_apply T hTarget Q hLabels ω u

end DiamondIntegral.Section3

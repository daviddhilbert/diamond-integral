import «section 3».GammaNormalizedFullMeasure
import «section 3».GammaFullLabelDescent
import «section 3».GammaNativeChainDensity

/-! An actual full measured native VF bijection over an actual native RV
isomorphism descends to the measured full-weight RV category in every
positive degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def gammaNativeFullLabelMeasuredHom (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (e : GammaIsoAt U V)
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η))
    (hl : ∀ p, gammaNativeLiftLabel V (f.map.map p) =
      (Section5.nativeRVGroundIso e).map (gammaNativeLiftLabel U p)) :
    GammaGroundMeasuredRVHom (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V η) := by
  let E := Section5.nativeRVGroundIso (hc := hc) e
  let H := Section5.nativeRVGroundIso (hc := hc) (gammaNativeHighRestrictionIso e)
  let sq := gammaNativeHighIso_square (hc := hc) e
  let F := gammaNormalizedFullMeasured hκ.le hs hr hv U V ω η E H sq f hl
  refine ⟨H,?_⟩
  exact gammaFullLabelDescent hκ hs h00 hr
    (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V η) H F.map
    (gammaNormalizedLiftBijection_label U V E H sq f.map hl) F.measure

end DiamondIntegral.Section3

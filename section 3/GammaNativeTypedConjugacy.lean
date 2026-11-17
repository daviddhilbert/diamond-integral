import «section 3».GammaNativeTypedMeasuredBridge
import «section 3».GammaGroundPointIsomorphisms

/-! A full native measured bijection gives the identical mixed point
bijection on typed presentations, with its full original Gamma graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (U V : GammaObjectAt B Set.univ n)
variable (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
variable (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
variable (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η))

def gammaNativeTypedFullConjugate : GammaFullMeasuredBijection
    (gammaNativeTypedMeasuredData U ω) (gammaNativeTypedMeasuredData V η) :=
  ((gammaNativeTypedFullMeasured hκ hs hr hv U ω).comp hκ hs hr hv f).comp hκ hs hr hv
    ((gammaNativeTypedFullMeasured hκ hs hr hv V η).symm hκ hs hr hv)

def gammaNativeTypedMeasuredMap : Map (typedLift U.object.obj) (typedLift V.object.obj) :=
  gammaGroundPointMap (gammaNativeTypedLift_definable U) (gammaNativeTypedLift_definable V)
    (gammaNativeTypedFullConjugate hκ hs hr hv U V ω η f).map

theorem gammaNativeTypedMeasuredMap_bijective :
    Function.Bijective (gammaNativeTypedMeasuredMap hκ hs hr hv U V ω η f) :=
  (gammaNativeTypedFullConjugate hκ hs hr hv U V ω η f).map.bijective

theorem gammaNativeTypedMeasuredMap_graph :
    GammaGraphDefinable B (pointMapGraph (gammaNativeTypedMeasuredMap hκ hs hr hv U V ω η f)) :=
  (gammaGroundPointIso (gammaNativeTypedFullConjugate hκ hs hr hv U V ω η f).map).graph

theorem gammaNativeTypedMeasuredMap_source_inverse
    (p : (gammaNativeUnitLift (hc := hc) U.toGamma).domain) :
    gammaNativeTypedMeasuredMap hκ hs hr hv U V ω η f ((gammaNativeTypedLiftBijection U).symm.map p) =
      (gammaNativeTypedLiftBijection V).symm.map (f.map.map p) := by
  change (gammaNativeTypedLiftBijection V).symm.map (f.map.map
    ((gammaNativeTypedLiftBijection U).map ((gammaNativeTypedLiftBijection U).symm.map p))) = _
  exact congrArg (fun q => (gammaNativeTypedLiftBijection V).symm.map (f.map.map q))
    ((gammaNativeTypedLiftBijection U).map.apply_inverse (gammaNativeTypedLiftBijection U).bijective p)

end DiamondIntegral.Section3

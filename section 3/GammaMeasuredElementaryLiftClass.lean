import «section 3».GammaMeasuredElementaryNormalization
import «section 3».GammaNativeMeasuredElementaryLift
import «section 3».GammaMeasuredClosureClassLift

/-! The actual native elementary special bijection and the weighted
principal-congruence object have the same measured VF class. -/
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMeasuredElementary_lift_class
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hB : VFGammaGeneratedBase (closureBase B))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : GammaGroundMeasuredRVObject hc B (n+1)) (i : Fin (n+1))
    (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject i)
    (D : ElementaryLiftDiagram (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject i) :
    gammaGroundMeasuredVFClass hκ.le hs hr hv (gammaGroundMeasuredObjectLift U) =
      gammaGroundMeasuredVFClass hκ.le hs hr hv
        (gammaGroundMeasuredObjectLift (gammaMeasuredElementaryObject hκ.le hs h00 hr U i hAd)) := by
  let A := Section5.groundRVAt U.underlying
  let ω := U.form.comp (Section5.groundRVObjectRoundTrip U.underlying).map
  let E := gammaElementaryAt hκ.le hs h00 hr A i hAd
  let ρ := ω.comp (gammaNativeElementaryOldLabel hκ.le hs h00 hr A i hAd)
  calc
    _ = gammaGroundMeasuredVFClass hκ.le hs hr hv (gammaNativeMeasuredLift A ω) :=
      (gammaGroundMeasuredVFClass_iso hκ.le hs hr hv (gammaNativeMeasuredLiftBridge hκ.le hs hr hv U)).symm
    _ = gammaGroundMeasuredVFClass hκ.le hs hr hv (gammaNativeMeasuredLift E ρ) :=
      gammaGroundMeasuredVFClass_iso hκ.le hs hr hv
        (gammaNativeMeasuredElementaryHom hκ.le hs h00 hr hv A i hAd D ω)
    _ = gammaGroundMeasuredVFClass hκ.le hs hr hv
        (gammaGroundMeasuredObjectLift (gammaNativeMeasuredNormalization E ρ)) :=
      gammaNativeMeasuredNormalization_lift_class hκ.le hs hr hv E ρ
    _ = _ := gammaGroundMeasuredVFClass_iso hκ.le hs hr hv
      (gammaMeasuredClosureArrowLift hκ hs h00 hr hg hB hv
        (gammaMeasuredElementaryNormalizationHom hκ.le hs h00 hr U i hAd))

end DiamondIntegral.Section3

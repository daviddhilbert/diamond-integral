import «section 3».GammaNormalizedLiftBijections
import «section 3».GammaFullMeasuredBijections

/-! Restricting a label-compatible full native measured bijection to the
full-weight local lifts retains the complete Gamma Jacobian identity. -/
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
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def gammaNormalizedFullMeasured (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (E : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain V))
    (H : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U))
      (Section5.nativeRVGroundDomain (gammaHighRestrictionAt V)))
    (hSquare : ∀ u, gammaNativeHighLabelInclusion V (H.map u) = E.map (gammaNativeHighLabelInclusion U u))
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η))
    (hl : ∀ p, gammaNativeLiftLabel V (f.map.map p) = E.map (gammaNativeLiftLabel U p)) :
    GammaFullMeasuredBijection
      (gammaGroundMeasuredObjectLift (gammaNativeMeasuredNormalization U ω))
      (gammaGroundMeasuredObjectLift (gammaNativeMeasuredNormalization V η)) := by
  let g := gammaNormalizedLiftBijection U V E H hSquare f.map hl
  refine ⟨g,?_⟩
  intro p hp
  let i := gammaNormalizedLiftInclusion (hc := hc) U
  obtain ⟨L,F,hF,hFL⟩ := gammaGround_differentiable_of_independent hκ hs hr hv g.map p hp
  let K := (LinearMap.toMatrix' L).det
  have hK : HasMixedVFJacobianAt g.map p K := ⟨F,hF,hFL.hasJacobianAt⟩
  obtain ⟨J,hJ,hw⟩ := f.measure (i p) hp
  have hJK := mixedJacobian_eq_of_restriction f.map.map g.map i (fun _ => rfl)
    (gammaNormalizedLiftBijection_val U V E H hSquare f.map hl) p hJ hK
  refine ⟨K,hK,?_⟩
  have hSource : gammaGroundMeasuredVFWeight (gammaGroundMeasuredObjectLift (gammaNativeMeasuredNormalization U ω)) p =
      gammaGroundMeasuredVFWeight (gammaNativeMeasuredLift U ω) (i p) := by rfl
  have hTarget : gammaGroundMeasuredVFWeight (gammaGroundMeasuredObjectLift (gammaNativeMeasuredNormalization V η)) (g.map p) =
      gammaGroundMeasuredVFWeight (gammaNativeMeasuredLift V η) (f.map.map (i p)) := by
    change (gammaGroundFormValue η (gammaNativeHighLabelInclusion V
      (gammaGroundObjectLiftLabel (gammaNativeMeasuredNormalization V η).underlying (g.map p)))).val =
        (gammaGroundFormValue η (gammaNativeLiftLabel V (f.map.map (i p)))).val
    rfl
  rw [hSource,hTarget,← hJK]
  exact hw

end DiamondIntegral.Section3

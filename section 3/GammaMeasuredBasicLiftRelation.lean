import «section 3».GammaBasicUnitLiftCarriers
import «section 3».GammaBasicConeNonzero
import «section 3».GammaElementaryClosureExistence
import «section 3».GammaMeasuredClosureClassLift

/-! The homogeneous measured point/cone relation holds for the actual
VF lifts, over the original Gamma ground and before groupification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMeasuredBasic_lift_class
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hB : VFGammaGeneratedBase (closureBase B))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    gammaGroundMeasuredVFClass hκ.le hs hr hv (gammaGroundMeasuredObjectLift (gammaGroundMeasuredRVOne hc B)) =
      gammaGroundMeasuredVFClass hκ.le hs hr hv (gammaGroundMeasuredObjectLift (gammaGroundMeasuredRVPositive hc B)) := by
  let P := gammaOneAt (B := B) (S := Set.univ) (Set.subset_univ _)
  let E := gammaElementaryAt hκ.le hs h00 hr P 0 (gammaOneAt_admissible (Set.subset_univ _))
  let Q := gammaPositiveAt (B := B) (S := Set.univ) (Set.subset_univ _)
  obtain ⟨D⟩ := gammaElementaryDiagram_exists_original hκ hs h00 hr hg hB
    (U := P.toGamma.toGammaRVObject) (Set.subset_univ _) (gammaOneAt_admissible (Set.subset_univ _))
  have hP := gammaMeasuredHomOfCarrierEq hκ.le hs hr hv
    (U := gammaNativeUnitLift (hc := hc) P.toGamma)
    (V := gammaGroundMeasuredObjectLift (gammaMeasuredPointZeroArity hc B)) rfl
    (heq_of_eq (gammaDefSet_eq_of_carrierEq gammaBasicPoint_lift_carrier)) (fun _ _ _ => rfl)
  have hE := gammaMeasuredHomOfCarrierEq hκ.le hs hr hv
    (U := gammaNativeUnitLift (hc := hc) E.toGamma) (V := gammaNativeUnitLift (hc := hc) Q.toGamma) rfl
    (heq_of_eq (gammaDefSet_eq_of_carrierEq (gammaBasicElementary_positive_lift_carrier hκ.le hs h00 hr)))
    (fun _ _ _ => rfl)
  have h0 := gammaGroundMeasuredVFClass_iso hκ.le hs hr hv
    (gammaMeasuredClosureArrowLift hκ hs h00 hr hg hB hv (gammaMeasuredPointZeroArityHom hc B))
  exact h0.symm.trans ((gammaGroundMeasuredVFClass_iso hκ.le hs hr hv hP).symm.trans
    ((gammaGroundMeasuredVFClass_iso hκ.le hs hr hv
      (gammaNativeUnitElementaryHom hκ.le hs h00 hr hv P 0 (gammaOneAt_admissible (Set.subset_univ _)) D)).trans
      ((gammaGroundMeasuredVFClass_iso hκ.le hs hr hv hE).trans (gammaBasicPositive_cone_class hκ.le hs hr hv))))

end DiamondIntegral.Section3

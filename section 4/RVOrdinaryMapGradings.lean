import «section 4».RVOrdinaryRadius
import «section 4».RVOrdinaryGrading
import «section 4».RESOrdinaryGrading
import «section 4».CoactionGradedMaps

/-! The actual ordinary RES inclusion and both forgetful maps preserve
the full natural-number grading, including after the bounded radius
quotient. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVOrdinaryMapGradings
open RVMeasuredCharts RVOrdinaryMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem ofRES_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (ofRES B)).comp (RESOrdinaryGrading.coaction B) =
      (RVOrdinaryGrading.coaction B).comp (ofRES B) := by
  apply RESOrdinaryRing.hom_ext B
  intro n a
  change (RESOrdinaryGrading.coaction B (RESOrdinaryRing.objectClass a)).map (ofRES B) =
    RVOrdinaryGrading.coaction B (ofRES B (RESOrdinaryRing.objectClass a))
  rw [RESOrdinaryGrading.coaction_class, Polynomial.map_monomial,
    ofRES_class, RVOrdinaryGrading.coaction_class]

theorem ofRES_mem (B : Base (M := M)) {n : ℕ} {x : RESOrdinaryRing.Ring B}
    (hx : x ∈ RESOrdinaryGrading.gradedPiece B n) :
    ofRES B x ∈ RVOrdinaryGrading.gradedPiece B n := by
  change RESOrdinaryGrading.coaction B x = Polynomial.monomial n x at hx
  change RVOrdinaryGrading.coaction B (ofRES B x) = Polynomial.monomial n (ofRES B x)
  have he := RingHom.congr_fun (ofRES_coaction B) x
  change (RESOrdinaryGrading.coaction B x).map (ofRES B) = RVOrdinaryGrading.coaction B (ofRES B x) at he
  rw [← he, hx, Polynomial.map_monomial]

def gradedOfRES (B : Base (M := M)) :
    GradedRingHom (RESOrdinaryGrading.gradedPiece B) (RVOrdinaryGrading.gradedPiece B) where
  toRingHom := ofRES B
  map_mem := fun hx => ofRES_mem B hx

theorem boundedForget_mem (B : Base (M := M)) {n : ℕ} {x : RVBoundedRing.Ring B}
    (hx : x ∈ RVBoundedGrading.gradedPiece B n) :
    boundedForget B x ∈ RVOrdinaryGrading.gradedPiece B n :=
  RVOrdinaryGrading.forget_mem B (RVBoundedMaps.forget_mem B hx)

def gradedBoundedForget (B : Base (M := M)) :
    GradedRingHom (RVBoundedGrading.gradedPiece B) (RVOrdinaryGrading.gradedPiece B) where
  toRingHom := boundedForget B
  map_mem := fun hx => boundedForget_mem B hx

theorem radiusForget_mem (B : Base (M := M)) {n : ℕ} {x : RVRadiusQuotient.Ring B}
    (hx : x ∈ RVRadiusQuotient.piece B n) :
    RVOrdinaryRadius.forget B x ∈ RVOrdinaryGrading.gradedPiece B n :=
  (RVBoundedGrading.gradingCoaction B).quotientLift_mem (RVOrdinaryGrading.gradingCoaction B)
    (boundedForget B) (RVRadiusIdeal.radiusIdeal B) (RVRadiusQuotient.ideal_coefficients B)
    (RVOrdinaryRadius.radiusIdeal_le_ker B) (fun _ _ hx => boundedForget_mem B hx) hx

def gradedRadiusForget (B : Base (M := M)) :
    GradedRingHom (RVRadiusQuotient.piece B) (RVOrdinaryGrading.gradedPiece B) where
  toRingHom := RVOrdinaryRadius.forget B
  map_mem := fun hx => radiusForget_mem B hx

end DiamondIntegral.Section4.RVOrdinaryMapGradings

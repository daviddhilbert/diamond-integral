import «section 4».RVOrdinaryDisjointPresentation
import «section 4».RVOrdinaryFamilyGrading

/-! The ordinary object disjoint-union/scissor equivalence preserves the
full object-degree grading in both directions. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVOrdinaryDisjointGrading
open RVOrdinaryDisjointPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev piece (B : Base (M := M)) := RVOrdinaryFamilyGrading.piece (family B)

theorem toChart_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (toChartRing B)).comp (RVOrdinaryFamilyGrading.coaction (family B)) =
      (RVOrdinaryGrading.coaction B).comp (toChartRing B) :=
  RVOrdinaryFamilyGrading.map_coaction_of_classes (family B) (RVOrdinaryGrading.gradingCoaction B) (toChartRing B) (by
    intro n a
    change RVOrdinaryGrading.coaction B (toChartRing B (objectClass (fromObject a))) =
      Polynomial.monomial n (toChartRing B (objectClass (fromObject a)))
    rw [toChartRing_class]
    exact RVOrdinaryGrading.coaction_class B (fromObject a))

theorem fromChart_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (fromChartRing B)).comp (RVOrdinaryGrading.coaction B) =
      (RVOrdinaryFamilyGrading.coaction (family B)).comp (fromChartRing B) := by
  apply RVOrdinaryRing.hom_ext B
  intro n a
  change (RVOrdinaryGrading.coaction B (RVOrdinaryRing.objectClass a)).map (fromChartRing B) =
    RVOrdinaryFamilyGrading.coaction (family B) (fromChartRing B (RVOrdinaryRing.objectClass a))
  rw [RVOrdinaryGrading.coaction_class, Polynomial.map_monomial, fromChartRing_class]
  exact (RVOrdinaryFamilyGrading.coaction_class (family B) (toObject a)).symm

theorem toChart_mem (B : Base (M := M)) {n : ℕ} {x : Ring B} (hx : x ∈ piece B n) :
    toChartRing B x ∈ RVOrdinaryGrading.gradedPiece B n := by
  change RVOrdinaryFamilyGrading.coaction (family B) x = Polynomial.monomial n x at hx
  change RVOrdinaryGrading.coaction B (toChartRing B x) = Polynomial.monomial n (toChartRing B x)
  have he := RingHom.congr_fun (toChart_coaction B) x
  change (RVOrdinaryFamilyGrading.coaction (family B) x).map (toChartRing B) = RVOrdinaryGrading.coaction B (toChartRing B x) at he
  rw [← he, hx, Polynomial.map_monomial]

theorem fromChart_mem (B : Base (M := M)) {n : ℕ} {x : RVOrdinaryRing.Ring B} (hx : x ∈ RVOrdinaryGrading.gradedPiece B n) :
    fromChartRing B x ∈ piece B n := by
  change RVOrdinaryGrading.coaction B x = Polynomial.monomial n x at hx
  change RVOrdinaryFamilyGrading.coaction (family B) (fromChartRing B x) = Polynomial.monomial n (fromChartRing B x)
  have he := RingHom.congr_fun (fromChart_coaction B) x
  change (RVOrdinaryGrading.coaction B x).map (fromChartRing B) = RVOrdinaryFamilyGrading.coaction (family B) (fromChartRing B x) at he
  rw [← he, hx, Polynomial.map_monomial]

def gradedToChart (B : Base (M := M)) : GradedRingHom (piece B) (RVOrdinaryGrading.gradedPiece B) where
  toRingHom := toChartRing B
  map_mem := fun hx => toChart_mem B hx

def gradedFromChart (B : Base (M := M)) : GradedRingHom (RVOrdinaryGrading.gradedPiece B) (piece B) where
  toRingHom := fromChartRing B
  map_mem := fun hx => fromChart_mem B hx

theorem equivalence_mem_iff (B : Base (M := M)) (n : ℕ) (x : Ring B) :
    equivalence B x ∈ RVOrdinaryGrading.gradedPiece B n ↔ x ∈ piece B n := by
  change toChartRing B x ∈ RVOrdinaryGrading.gradedPiece B n ↔ x ∈ piece B n
  constructor
  · intro hx
    have h := fromChart_mem B hx
    have he := RingHom.congr_fun (from_to B) x
    change fromChartRing B (toChartRing B x) = x at he
    rwa [he] at h
  · exact toChart_mem B

end DiamondIntegral.Section4.RVOrdinaryDisjointGrading

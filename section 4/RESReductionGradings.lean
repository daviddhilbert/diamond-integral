import «section 4».RESOrdinaryGrading
import «section 4».PolynomialCoactionQuotient
import «section 4».RESMeasuredReduction
import «section 4».RESOrdinaryReduction

/-! The actual measured and ordinary RES reduction ideals are homogeneous.
Their quotient rings therefore inherit natural-number gradings. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESReductionGradings
open RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem measured_fibre_homogeneous (B : Base (M := M)) :
    (RESMeasuredReduction.fibreIdeal B).IsHomogeneous (RESRingCoaction.gradedPiece B) := by
  apply Ideal.homogeneous_span
  rintro x ⟨α, β, hα, hβ, rfl⟩
  exact ⟨1, (RESRingCoaction.gradedPiece B 1).sub_mem
    (RESRingCoaction.class_mem_gradedPiece B _) (RESRingCoaction.class_mem_gradedPiece B _)⟩

theorem measured_affine_mem (B : Base (M := M)) :
    RESMeasuredReduction.affineClass B ∈ RESRingCoaction.gradedPiece B 1 :=
  (RESRingCoaction.gradedPiece B 1).add_mem
    (RESRingCoaction.class_mem_gradedPiece B _) (RESRingCoaction.class_mem_gradedPiece B _)

theorem measured_reduction_homogeneous (B : Base (M := M)) :
    (RESMeasuredReduction.reductionIdeal B).IsHomogeneous (RESRingCoaction.gradedPiece B) := by
  apply Ideal.IsHomogeneous.sup (measured_fibre_homogeneous B)
  apply Ideal.homogeneous_span
  intro x hx
  have he : x = RESMeasuredReduction.affineClass B := Set.mem_singleton_iff.mp hx
  subst x
  exact ⟨1, measured_affine_mem B⟩

theorem measured_ideal_coefficients (B : Base (M := M)) :
    ∀ n x, x ∈ RESMeasuredReduction.reductionIdeal B →
      (RESRingCoaction.coaction B x).coeff n ∈ RESMeasuredReduction.reductionIdeal B :=
  (RESGrading.gradingCoaction B).homogeneous_ideal_coefficients _ (measured_reduction_homogeneous B)

def measuredCoaction (B : Base (M := M)) :
    PolynomialCoactionGrading.Coaction (RESMeasuredReduction.ReducedRing B) :=
  (RESGrading.gradingCoaction B).quotient _ (measured_ideal_coefficients B)

def measuredPiece (B : Base (M := M)) (n : ℕ) : AddSubgroup (RESMeasuredReduction.ReducedRing B) :=
  (measuredCoaction B).piece n

instance measuredGradedRing (B : Base (M := M)) : GradedRing (measuredPiece B) :=
  (measuredCoaction B).grading

theorem measured_quotient_mem (B : Base (M := M)) {n : ℕ} {x : RESChartRing.Ring B}
    (hx : x ∈ RESRingCoaction.gradedPiece B n) :
    RESMeasuredReduction.quotient B x ∈ measuredPiece B n :=
  (RESGrading.gradingCoaction B).quotient_mem _ (measured_ideal_coefficients B) hx

theorem measured_class_mem (B : Base (M := M)) {n : ℕ} (a : RESChart B n) :
    RESMeasuredReduction.quotient B (RESChartRing.objectClass a) ∈ measuredPiece B n :=
  measured_quotient_mem B (RESRingCoaction.class_mem_gradedPiece B a)

theorem measured_torus_mem (B : Base (M := M)) :
    RESMeasuredReduction.torusClass B ∈ measuredPiece B 1 := measured_class_mem B _

theorem measured_point_mem (B : Base (M := M)) :
    RESMeasuredReduction.pointClass B ∈ measuredPiece B 1 := measured_class_mem B _

theorem measured_weight_mem (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) :
    RESMeasuredReduction.weightValue B γ hγ ∈ measuredPiece B 0 := measured_class_mem B _

theorem ordinary_fibre_homogeneous (B : Base (M := M)) :
    (RESOrdinaryReduction.fibreIdeal B).IsHomogeneous (RESOrdinaryGrading.gradedPiece B) := by
  apply Ideal.homogeneous_span
  rintro x ⟨α, hα, rfl⟩
  exact ⟨1, (RESOrdinaryGrading.gradedPiece B 1).sub_mem
    (RESOrdinaryGrading.class_mem B _) (RESOrdinaryGrading.class_mem B _)⟩

theorem ordinary_ideal_coefficients (B : Base (M := M)) :
    ∀ n x, x ∈ RESOrdinaryReduction.fibreIdeal B →
      (RESOrdinaryGrading.coaction B x).coeff n ∈ RESOrdinaryReduction.fibreIdeal B :=
  (RESOrdinaryGrading.gradingCoaction B).homogeneous_ideal_coefficients _ (ordinary_fibre_homogeneous B)

def ordinaryCoaction (B : Base (M := M)) :
    PolynomialCoactionGrading.Coaction (RESOrdinaryReduction.ReducedRing B) :=
  (RESOrdinaryGrading.gradingCoaction B).quotient _ (ordinary_ideal_coefficients B)

def ordinaryPiece (B : Base (M := M)) (n : ℕ) : AddSubgroup (RESOrdinaryReduction.ReducedRing B) :=
  (ordinaryCoaction B).piece n

instance ordinaryGradedRing (B : Base (M := M)) : GradedRing (ordinaryPiece B) :=
  (ordinaryCoaction B).grading

theorem ordinary_quotient_mem (B : Base (M := M)) {n : ℕ} {x : RESOrdinaryRing.Ring B}
    (hx : x ∈ RESOrdinaryGrading.gradedPiece B n) :
    RESOrdinaryReduction.quotient B x ∈ ordinaryPiece B n :=
  (RESOrdinaryGrading.gradingCoaction B).quotient_mem _ (ordinary_ideal_coefficients B) hx

theorem ordinary_class_mem (B : Base (M := M)) {n : ℕ} (a : RESChart B n) :
    RESOrdinaryReduction.quotient B (RESOrdinaryRing.objectClass a) ∈ ordinaryPiece B n :=
  ordinary_quotient_mem B (RESOrdinaryGrading.class_mem B a)

theorem forget_mem (B : Base (M := M)) {n : ℕ} {x : RESChartRing.Ring B}
    (hx : x ∈ RESRingCoaction.gradedPiece B n) :
    RESOrdinaryReduction.forget B x ∈ ordinaryPiece B n :=
  ordinary_quotient_mem B (RESOrdinaryGrading.forget_mem B hx)

end DiamondIntegral.Section4.RESReductionGradings

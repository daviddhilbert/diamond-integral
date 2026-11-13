import «section 4».TensorCoactionGrading
import «section 4».GammaFiniteRVMapGradings
import «section 4».RVFiniteBalancedTensor
import «section 4».RVBoundedBalancedTensor

/-! Both actual tensors over the intrinsic finite-Gamma ring have full
natural-number gradings, with homogeneous pure tensors in the sum degree. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVBalancedGradings
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def measuredData (B : Base (M := M)) : TensorPolynomialCoaction.Data
    (GammaFiniteRVPresentation.ChartRing B) (RESChartRing.Ring B) (GammaRVChartPresentation.ChartRing B) where
  base := GammaFiniteRVGrading.gradingCoaction B
  left := RESGrading.gradingCoaction B
  right := GammaRVGrading.gradingCoaction B
  left_compatible := GammaFiniteRVGrading.map_coaction_of_classes B (RESGrading.gradingCoaction B)
    (GammaFiniteRVMaps.sharp B) (fun _ a =>
      (GammaFiniteRVMapGradings.gradedSharp B).map_mem (GammaFiniteRVGrading.class_mem B a))
  right_compatible := GammaFiniteRVGrading.map_coaction_of_classes B (GammaRVGrading.gradingCoaction B)
    (GammaFiniteRVMaps.forget B) (fun _ a =>
      (GammaFiniteRVMapGradings.gradedForget B).map_mem (GammaFiniteRVGrading.class_mem B a))

def boundedData (B : Base (M := M)) : TensorPolynomialCoaction.Data
    (GammaFiniteRVPresentation.ChartRing B) (RESChartRing.Ring B) (GammaBoundedRVPresentation.ChartRing B) where
  base := GammaFiniteRVGrading.gradingCoaction B
  left := RESGrading.gradingCoaction B
  right := GammaBoundedRVGrading.gradingCoaction B
  left_compatible := (measuredData B).left_compatible
  right_compatible := GammaFiniteRVGrading.map_coaction_of_classes B (GammaBoundedRVGrading.gradingCoaction B)
    (GammaFiniteRVMaps.bounded B) (fun _ a =>
      (GammaFiniteRVMapGradings.gradedBounded B).map_mem (GammaFiniteRVGrading.class_mem B a))

def measuredCoaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (RVFiniteBalancedTensor.Source B) :=
  TensorCoactionGrading.coaction (measuredData B)

def boundedCoaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (RVBoundedBalancedTensor.Source B) :=
  TensorCoactionGrading.coaction (boundedData B)

def measuredPiece (B : Base (M := M)) (n : ℕ) : AddSubgroup (RVFiniteBalancedTensor.Source B) := (measuredCoaction B).piece n

def boundedPiece (B : Base (M := M)) (n : ℕ) : AddSubgroup (RVBoundedBalancedTensor.Source B) := (boundedCoaction B).piece n

instance measuredGradedRing (B : Base (M := M)) : GradedRing (measuredPiece B) := (measuredCoaction B).grading

instance boundedGradedRing (B : Base (M := M)) : GradedRing (boundedPiece B) := (boundedCoaction B).grading

theorem measured_tmul_mem (B : Base (M := M)) {m n : ℕ} {x : RESChartRing.Ring B} {y : GammaRVChartPresentation.ChartRing B}
    (hx : x ∈ RESRingCoaction.gradedPiece B m) (hy : y ∈ GammaRVGrading.gradedPiece B n) :
    x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y ∈ measuredPiece B (m + n) :=
  TensorCoactionGrading.tmul_mem (measuredData B) hx hy

theorem bounded_tmul_mem (B : Base (M := M)) {m n : ℕ} {x : RESChartRing.Ring B} {y : GammaBoundedRVPresentation.ChartRing B}
    (hx : x ∈ RESRingCoaction.gradedPiece B m) (hy : y ∈ GammaBoundedRVGrading.gradedPiece B n) :
    x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y ∈ boundedPiece B (m + n) :=
  TensorCoactionGrading.tmul_mem (boundedData B) hx hy

end DiamondIntegral.Section4.RVBalancedGradings

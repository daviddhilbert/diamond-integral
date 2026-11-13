import «section 4».IntrinsicBalancedTensors
import «section 4».IntrinsicPresentationGradings
import «section 4».RVBalancedMapGradings

/-! The balanced tensors of intrinsic presentations have actual full
natural-number gradings. Their algebra equivalences preserve degrees in
both directions, and the actual product comparisons preserve degree. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.IntrinsicBalancedGradings
open IntrinsicBalancedTensors IntrinsicFiniteGammaAlgebras IntrinsicPresentationGradings
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def measuredData (B : Base (M := M)) : TensorPolynomialCoaction.Data (Coeff B)
    (RESDisjointPresentation.Ring B) (GammaRVFiniteUnionPresentation.Ring B) where
  base := GammaFiniteRVGrading.gradingCoaction B
  left := RVFamilyDisjointGrading.gradingCoaction (RESDisjointPresentation.family B)
  right := GammaRVFiniteUnionGrading.gradingCoaction B
  left_compatible := (GammaFiniteRVGrading.gradingCoaction B).map_coaction_of_mem
    (RVFamilyDisjointGrading.gradingCoaction (RESDisjointPresentation.family B))
    (algebraMap (Coeff B) (RESDisjointPresentation.Ring B)) (by
      intro n x hx
      rw [coefficient_res]
      exact finiteSharp_mem B (gammaFinite_inverse_mem B hx))
  right_compatible := (GammaFiniteRVGrading.gradingCoaction B).map_coaction_of_mem
    (GammaRVFiniteUnionGrading.gradingCoaction B)
    (algebraMap (Coeff B) (GammaRVFiniteUnionPresentation.Ring B)) (by
      intro n x hx
      rw [coefficient_gamma]
      exact gammaFiniteToFull_mem B (gammaFinite_inverse_mem B hx))

def boundedData (B : Base (M := M)) : TensorPolynomialCoaction.Data (Coeff B)
    (RESDisjointPresentation.Ring B) (GammaBoundedRVFiniteUnionPresentation.Ring B) where
  base := GammaFiniteRVGrading.gradingCoaction B
  left := RVFamilyDisjointGrading.gradingCoaction (RESDisjointPresentation.family B)
  right := GammaBoundedRVFiniteUnionGrading.gradingCoaction B
  left_compatible := (measuredData B).left_compatible
  right_compatible := (GammaFiniteRVGrading.gradingCoaction B).map_coaction_of_mem
    (GammaBoundedRVFiniteUnionGrading.gradingCoaction B)
    (algebraMap (Coeff B) (GammaBoundedRVFiniteUnionPresentation.Ring B)) (by
      intro n x hx
      rw [coefficient_boundedGamma]
      exact gammaFiniteToBounded_mem B (gammaFinite_inverse_mem B hx))

def measuredCoaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Source B) := TensorCoactionGrading.coaction (measuredData B)
def boundedCoaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (BoundedSource B) := TensorCoactionGrading.coaction (boundedData B)
def measuredPiece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Source B) := (measuredCoaction B).piece n
def boundedPiece (B : Base (M := M)) (n : ℕ) : AddSubgroup (BoundedSource B) := (boundedCoaction B).piece n
instance measuredGradedRing (B : Base (M := M)) : GradedRing (measuredPiece B) := (measuredCoaction B).grading
instance boundedGradedRing (B : Base (M := M)) : GradedRing (boundedPiece B) := (boundedCoaction B).grading

theorem measured_tmul_mem (B : Base (M := M)) {m n : ℕ} {x : RESDisjointPresentation.Ring B} {y : GammaRVFiniteUnionPresentation.Ring B}
    (hx : x ∈ RESDisjointGrading.piece B m) (hy : y ∈ GammaRVFiniteUnionGrading.piece B n) :
    x ⊗ₜ[Coeff B] y ∈ measuredPiece B (m + n) := TensorCoactionGrading.tmul_mem (measuredData B) hx hy

theorem bounded_tmul_mem (B : Base (M := M)) {m n : ℕ} {x : RESDisjointPresentation.Ring B} {y : GammaBoundedRVFiniteUnionPresentation.Ring B}
    (hx : x ∈ RESDisjointGrading.piece B m) (hy : y ∈ GammaBoundedRVFiniteUnionGrading.piece B n) :
    x ⊗ₜ[Coeff B] y ∈ boundedPiece B (m + n) := TensorCoactionGrading.tmul_mem (boundedData B) hx hy

theorem equivalence_mem (B : Base (M := M)) {n : ℕ} {x : Source B} (hx : x ∈ measuredPiece B n) :
    equivalence B x ∈ RVBalancedGradings.measuredPiece B n :=
  TensorGradedMaps.map_mem (measuredData B) (RVBalancedGradings.measuredCoaction B) (equivalence B).toAlgHom.toRingHom (by
    intro m n x y hx hy
    change equivalence B (x ⊗ₜ[Coeff B] y) ∈ RVBalancedGradings.measuredPiece B (m + n)
    rw [equivalence_tmul]
    exact RVBalancedGradings.measured_tmul_mem B (RESDisjointGrading.toChart_mem B hx) (GammaRVFiniteUnionGrading.toChart_mem B hy)) hx

theorem boundedEquivalence_mem (B : Base (M := M)) {n : ℕ} {x : BoundedSource B} (hx : x ∈ boundedPiece B n) :
    boundedEquivalence B x ∈ RVBalancedGradings.boundedPiece B n :=
  TensorGradedMaps.map_mem (boundedData B) (RVBalancedGradings.boundedCoaction B) (boundedEquivalence B).toAlgHom.toRingHom (by
    intro m n x y hx hy
    change boundedEquivalence B (x ⊗ₜ[Coeff B] y) ∈ RVBalancedGradings.boundedPiece B (m + n)
    rw [boundedEquivalence_tmul]
    exact RVBalancedGradings.bounded_tmul_mem B (RESDisjointGrading.toChart_mem B hx) (GammaBoundedRVFiniteUnionGrading.toChart_mem B hy)) hx

theorem inverse_mem (B : Base (M := M)) {n : ℕ} {x : RVFiniteBalancedTensor.Source B} (hx : x ∈ RVBalancedGradings.measuredPiece B n) :
    (equivalence B).symm x ∈ measuredPiece B n :=
  TensorGradedMaps.map_mem (RVBalancedGradings.measuredData B) (measuredCoaction B) (equivalence B).symm.toAlgHom.toRingHom (by
    intro m n x y hx hy
    change (equivalence B).symm (x ⊗ₜ[Coeff B] y) ∈ measuredPiece B (m + n)
    rw [equivalence_symm_tmul]
    exact measured_tmul_mem B (res_inverse_mem B hx) (gammaFull_inverse_mem B hy)) hx

theorem boundedInverse_mem (B : Base (M := M)) {n : ℕ} {x : RVBoundedBalancedTensor.Source B} (hx : x ∈ RVBalancedGradings.boundedPiece B n) :
    (boundedEquivalence B).symm x ∈ boundedPiece B n :=
  TensorGradedMaps.map_mem (RVBalancedGradings.boundedData B) (boundedCoaction B) (boundedEquivalence B).symm.toAlgHom.toRingHom (by
    intro m n x y hx hy
    change (boundedEquivalence B).symm (x ⊗ₜ[Coeff B] y) ∈ boundedPiece B (m + n)
    rw [boundedEquivalence_symm_tmul]
    exact bounded_tmul_mem B (res_inverse_mem B hx) (gammaBounded_inverse_mem B hy)) hx

theorem comparison_mem (B : Base (M := M)) {n : ℕ} {x : Source B} (hx : x ∈ measuredPiece B n) :
    comparison B x ∈ RVDisjointGrading.piece B n := by
  change (RVDisjointPresentation.equivalence B).symm (RVFiniteBalancedTensor.comparison B (equivalence B x)) ∈ _
  exact rvFull_inverse_mem B ((RVBalancedMapGradings.gradedMeasuredComparison B).map_mem (equivalence_mem B hx))

theorem boundedComparison_mem (B : Base (M := M)) {n : ℕ} {x : BoundedSource B} (hx : x ∈ boundedPiece B n) :
    boundedComparison B x ∈ RVBoundedDisjointGrading.piece B n := by
  change (RVBoundedDisjointPresentation.equivalence B).symm (RVBoundedBalancedTensor.comparison B (boundedEquivalence B x)) ∈ _
  exact rvBounded_inverse_mem B ((RVBalancedMapGradings.gradedBoundedComparison B).map_mem (boundedEquivalence_mem B hx))

end DiamondIntegral.Section4.IntrinsicBalancedGradings

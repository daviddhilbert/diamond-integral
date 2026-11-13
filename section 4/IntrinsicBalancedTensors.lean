import «section 4».IntrinsicFiniteGammaAlgebras
import «section 4».RVFiniteBalancedTensor
import «section 4».RVBoundedBalancedTensor

/-! Balanced tensors of the intrinsic RES and Gamma presentations.
Their algebra equivalences with the existing tensors transport the
actual product comparisons, with the expected pure-tensor formulas.
No comparison injectivity, surjectivity or global descent is assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.IntrinsicBalancedTensors
open IntrinsicFiniteGammaAlgebras
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Source (B : Base (M := M)) := RESDisjointPresentation.Ring B ⊗[Coeff B] GammaRVFiniteUnionPresentation.Ring B
abbrev BoundedSource (B : Base (M := M)) := RESDisjointPresentation.Ring B ⊗[Coeff B] GammaBoundedRVFiniteUnionPresentation.Ring B

def equivalence (B : Base (M := M)) : Source B ≃ₐ[Coeff B] RVFiniteBalancedTensor.Source B :=
  Algebra.TensorProduct.congr (resEquivalence B) (gammaEquivalence B)

def boundedEquivalence (B : Base (M := M)) : BoundedSource B ≃ₐ[Coeff B] RVBoundedBalancedTensor.Source B :=
  Algebra.TensorProduct.congr (resEquivalence B) (boundedGammaEquivalence B)

theorem equivalence_tmul (B : Base (M := M)) (x : RESDisjointPresentation.Ring B) (y : GammaRVFiniteUnionPresentation.Ring B) :
    equivalence B (x ⊗ₜ[Coeff B] y) = resEquivalence B x ⊗ₜ[Coeff B] gammaEquivalence B y := rfl

theorem boundedEquivalence_tmul (B : Base (M := M)) (x : RESDisjointPresentation.Ring B) (y : GammaBoundedRVFiniteUnionPresentation.Ring B) :
    boundedEquivalence B (x ⊗ₜ[Coeff B] y) = resEquivalence B x ⊗ₜ[Coeff B] boundedGammaEquivalence B y := rfl

theorem equivalence_symm_tmul (B : Base (M := M)) (x : RESChartRing.Ring B) (y : GammaRVChartPresentation.ChartRing B) :
    (equivalence B).symm (x ⊗ₜ[Coeff B] y) = (resEquivalence B).symm x ⊗ₜ[Coeff B] (gammaEquivalence B).symm y := rfl

theorem boundedEquivalence_symm_tmul (B : Base (M := M)) (x : RESChartRing.Ring B) (y : GammaBoundedRVPresentation.ChartRing B) :
    (boundedEquivalence B).symm (x ⊗ₜ[Coeff B] y) = (resEquivalence B).symm x ⊗ₜ[Coeff B] (boundedGammaEquivalence B).symm y := rfl

def comparison (B : Base (M := M)) : Source B →ₐ[Coeff B] RVDisjointPresentation.Ring B :=
  (rvEquivalence B).symm.toAlgHom.comp ((RVFiniteBalancedTensor.comparison B).comp (equivalence B).toAlgHom)

def boundedComparison (B : Base (M := M)) : BoundedSource B →ₐ[Coeff B] RVBoundedDisjointPresentation.Ring B :=
  (boundedRVEquivalence B).symm.toAlgHom.comp ((RVBoundedBalancedTensor.comparison B).comp (boundedEquivalence B).toAlgHom)

theorem comparison_tmul (B : Base (M := M)) (x : RESDisjointPresentation.Ring B) (y : GammaRVFiniteUnionPresentation.Ring B) :
    comparison B (x ⊗ₜ[Coeff B] y) = IntrinsicPresentationMaps.resToFull B x * IntrinsicPresentationMaps.fullSharp B y := by
  change (RVDisjointPresentation.equivalence B).symm
    (RVFiniteBalancedTensor.comparison B (equivalence B (x ⊗ₜ[Coeff B] y))) = _
  rw [equivalence_tmul, RVFiniteBalancedTensor.comparison_tmul, map_mul]
  rfl

theorem boundedComparison_tmul (B : Base (M := M)) (x : RESDisjointPresentation.Ring B) (y : GammaBoundedRVFiniteUnionPresentation.Ring B) :
    boundedComparison B (x ⊗ₜ[Coeff B] y) = IntrinsicPresentationMaps.resToBounded B x * IntrinsicPresentationMaps.boundedSharp B y := by
  change (RVBoundedDisjointPresentation.equivalence B).symm
    (RVBoundedBalancedTensor.comparison B (boundedEquivalence B (x ⊗ₜ[Coeff B] y))) = _
  rw [boundedEquivalence_tmul, RVBoundedBalancedTensor.comparison_tmul, map_mul]
  rfl

theorem comparison_square (B : Base (M := M)) :
    (rvEquivalence B).toAlgHom.comp (comparison B) = (RVFiniteBalancedTensor.comparison B).comp (equivalence B).toAlgHom := by
  apply DFunLike.ext
  intro x
  exact (rvEquivalence B).apply_symm_apply _

theorem boundedComparison_square (B : Base (M := M)) :
    (boundedRVEquivalence B).toAlgHom.comp (boundedComparison B) =
      (RVBoundedBalancedTensor.comparison B).comp (boundedEquivalence B).toAlgHom := by
  apply DFunLike.ext
  intro x
  exact (boundedRVEquivalence B).apply_symm_apply _

end DiamondIntegral.Section4.IntrinsicBalancedTensors

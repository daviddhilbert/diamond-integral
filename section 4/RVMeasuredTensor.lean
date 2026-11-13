import «section 4».GammaRVMapGradings
import «section 4».RVChartMaps
import Mathlib.RingTheory.TensorProduct.Maps

/-! Product comparison and evaluation on the tensor product over integers.
This is not yet the manuscript tensor product over finite Gamma objects:
finite-Gamma balancing, its kernel and global RV descent remain open. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVMeasuredTensor
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Source (B : Base (M := M)) :=
  RESChartRing.Ring B ⊗[ℤ] GammaRVChartPresentation.ChartRing B

def comparison (B : Base (M := M)) : Source B →ₐ[ℤ] RVChartRing.Ring B :=
  Algebra.TensorProduct.lift (RVChartMaps.ofRES B).toIntAlgHom (RVSharpRingMap.sharp B).toIntAlgHom
    (fun _ _ => Commute.all _ _)

theorem comparison_tmul (B : Base (M := M)) (x : RESChartRing.Ring B) (y : GammaRVChartPresentation.ChartRing B) :
    comparison B (x ⊗ₜ[ℤ] y) = RVChartMaps.ofRES B x * RVSharpRingMap.sharp B y := rfl

def evaluation (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    Source B →ₐ[ℤ] RESMeasuredReduction.ReducedRing B :=
  Algebra.TensorProduct.lift (RESMeasuredReduction.quotient B).toIntAlgHom
    (GammaRVMapGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom.toIntAlgHom
    (fun _ _ => Commute.all _ _)

theorem evaluation_tmul (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (x : RESChartRing.Ring B) (y : GammaRVChartPresentation.ChartRing B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[ℤ] y) =
      RESMeasuredReduction.quotient B x *
        GammaRVMapGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k y := rfl

end DiamondIntegral.Section4.RVMeasuredTensor
